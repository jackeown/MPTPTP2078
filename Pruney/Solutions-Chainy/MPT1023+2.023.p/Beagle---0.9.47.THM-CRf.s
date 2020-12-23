%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 10.31s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :  329 (5540 expanded)
%              Number of leaves         :   38 (1776 expanded)
%              Depth                    :   18
%              Number of atoms          :  589 (15849 expanded)
%              Number of equality atoms :  180 (2067 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_5',E_60) = k1_funct_1('#skF_6',E_60)
      | ~ m1_subset_1(E_60,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_137,plain,(
    ! [B_10] :
      ( k1_funct_1('#skF_5',B_10) = k1_funct_1('#skF_6',B_10)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_128])).

tff(c_260,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7588,plain,(
    ! [A_608,B_609,D_610] :
      ( r2_relset_1(A_608,B_609,D_610,D_610)
      | ~ m1_subset_1(D_610,k1_zfmisc_1(k2_zfmisc_1(A_608,B_609))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7609,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_7588])).

tff(c_156,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_283,plain,(
    ! [A_83,C_84,B_85] :
      ( m1_subset_1(A_83,C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7694,plain,(
    ! [A_621,B_622,A_623] :
      ( m1_subset_1(A_621,B_622)
      | ~ r2_hidden(A_621,A_623)
      | ~ r1_tarski(A_623,B_622) ) ),
    inference(resolution,[status(thm)],[c_28,c_283])).

tff(c_8144,plain,(
    ! [B_674,B_675,A_676] :
      ( m1_subset_1(B_674,B_675)
      | ~ r1_tarski(A_676,B_675)
      | ~ m1_subset_1(B_674,A_676)
      | v1_xboole_0(A_676) ) ),
    inference(resolution,[status(thm)],[c_18,c_7694])).

tff(c_8157,plain,(
    ! [B_674] :
      ( m1_subset_1(B_674,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_674,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_173,c_8144])).

tff(c_8158,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8157])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_174,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_156])).

tff(c_245,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(B_75,A_76)
      | ~ m1_subset_1(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_273,plain,(
    ! [A_81,B_82] :
      ( ~ r1_tarski(A_81,B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_245,c_36])).

tff(c_280,plain,
    ( ~ m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_273])).

tff(c_282,plain,(
    ~ m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_304,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_282])).

tff(c_305,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_281,plain,
    ( ~ m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_173,c_273])).

tff(c_311,plain,(
    ~ m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_315,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_311])).

tff(c_316,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_2739,plain,(
    ! [A_260,B_261,D_262] :
      ( r2_relset_1(A_260,B_261,D_262,D_262)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2760,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_2739])).

tff(c_184,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_211,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_184])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2888,plain,(
    ! [A_285,B_286,C_287] :
      ( k1_relset_1(A_285,B_286,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2924,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2888])).

tff(c_3107,plain,(
    ! [B_305,A_306,C_307] :
      ( k1_xboole_0 = B_305
      | k1_relset_1(A_306,B_305,C_307) = A_306
      | ~ v1_funct_2(C_307,A_306,B_305)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_306,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3129,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3107])).

tff(c_3147,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2924,c_3129])).

tff(c_3155,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3147])).

tff(c_210,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_184])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2923,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_2888])).

tff(c_3126,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3107])).

tff(c_3144,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2923,c_3126])).

tff(c_3149,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3144])).

tff(c_3370,plain,(
    ! [A_329,B_330] :
      ( r2_hidden('#skF_2'(A_329,B_330),k1_relat_1(A_329))
      | B_330 = A_329
      | k1_relat_1(B_330) != k1_relat_1(A_329)
      | ~ v1_funct_1(B_330)
      | ~ v1_relat_1(B_330)
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3983,plain,(
    ! [A_371,B_372] :
      ( m1_subset_1('#skF_2'(A_371,B_372),k1_relat_1(A_371))
      | B_372 = A_371
      | k1_relat_1(B_372) != k1_relat_1(A_371)
      | ~ v1_funct_1(B_372)
      | ~ v1_relat_1(B_372)
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(resolution,[status(thm)],[c_3370,c_24])).

tff(c_3992,plain,(
    ! [B_372] :
      ( m1_subset_1('#skF_2'('#skF_6',B_372),'#skF_3')
      | B_372 = '#skF_6'
      | k1_relat_1(B_372) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_372)
      | ~ v1_relat_1(B_372)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_3983])).

tff(c_4257,plain,(
    ! [B_390] :
      ( m1_subset_1('#skF_2'('#skF_6',B_390),'#skF_3')
      | B_390 = '#skF_6'
      | k1_relat_1(B_390) != '#skF_3'
      | ~ v1_funct_1(B_390)
      | ~ v1_relat_1(B_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_66,c_3149,c_3992])).

tff(c_60,plain,(
    ! [E_43] :
      ( k1_funct_1('#skF_5',E_43) = k1_funct_1('#skF_6',E_43)
      | ~ m1_subset_1(E_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_4285,plain,(
    ! [B_395] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_395)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_395))
      | B_395 = '#skF_6'
      | k1_relat_1(B_395) != '#skF_3'
      | ~ v1_funct_1(B_395)
      | ~ v1_relat_1(B_395) ) ),
    inference(resolution,[status(thm)],[c_4257,c_60])).

tff(c_32,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_2'(A_18,B_22)) != k1_funct_1(A_18,'#skF_2'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4292,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4285,c_32])).

tff(c_4299,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_72,c_3155,c_210,c_66,c_3155,c_3149,c_4292])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_4317,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4299,c_58])).

tff(c_4328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_4317])).

tff(c_4329,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3147])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4363,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4361,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_4329,c_12])).

tff(c_306,plain,(
    ! [A_86] :
      ( m1_subset_1(A_86,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_86,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_283])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_310,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_86,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_306,c_22])).

tff(c_2819,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_4424,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4361,c_2819])).

tff(c_4435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4424])).

tff(c_4436,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3144])).

tff(c_4470,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_6])).

tff(c_4468,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_4436,c_12])).

tff(c_4522,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4468,c_2819])).

tff(c_4533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4470,c_4522])).

tff(c_4535,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_110,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_4541,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4535,c_113])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4567,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4541,c_10])).

tff(c_4678,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4567])).

tff(c_4705,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4678,c_6])).

tff(c_4707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_4705])).

tff(c_4708,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4567])).

tff(c_4545,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4541,c_311])).

tff(c_4722,plain,(
    ~ m1_subset_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4708,c_4545])).

tff(c_4947,plain,(
    ! [A_417] :
      ( v1_xboole_0(A_417)
      | ~ r2_hidden(A_417,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_4955,plain,
    ( v1_xboole_0('#skF_1'('#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_4947])).

tff(c_4961,plain,(
    v1_xboole_0('#skF_1'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_4955])).

tff(c_4742,plain,(
    ! [A_52] :
      ( A_52 = '#skF_4'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4708,c_113])).

tff(c_4967,plain,(
    '#skF_1'('#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4961,c_4742])).

tff(c_120,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_124,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_4974,plain,
    ( m1_subset_1('#skF_4','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4967,c_124])).

tff(c_4984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_4722,c_4974])).

tff(c_4986,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_5103,plain,(
    ! [A_427,B_428,C_429] :
      ( k1_relset_1(A_427,B_428,C_429) = k1_relat_1(C_429)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5132,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_5103])).

tff(c_4993,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4986,c_113])).

tff(c_56,plain,(
    ! [B_37,A_36,C_38] :
      ( k1_xboole_0 = B_37
      | k1_relset_1(A_36,B_37,C_38) = A_36
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5482,plain,(
    ! [B_478,A_479,C_480] :
      ( B_478 = '#skF_6'
      | k1_relset_1(A_479,B_478,C_480) = A_479
      | ~ v1_funct_2(C_480,A_479,B_478)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_479,B_478))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4993,c_56])).

tff(c_5510,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5482])).

tff(c_5523,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5132,c_5510])).

tff(c_5534,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5523])).

tff(c_5131,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_5103])).

tff(c_5507,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5482])).

tff(c_5520,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5131,c_5507])).

tff(c_5524,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5520])).

tff(c_5599,plain,(
    ! [A_487,B_488] :
      ( r2_hidden('#skF_2'(A_487,B_488),k1_relat_1(A_487))
      | B_488 = A_487
      | k1_relat_1(B_488) != k1_relat_1(A_487)
      | ~ v1_funct_1(B_488)
      | ~ v1_relat_1(B_488)
      | ~ v1_funct_1(A_487)
      | ~ v1_relat_1(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6450,plain,(
    ! [A_536,B_537] :
      ( m1_subset_1('#skF_2'(A_536,B_537),k1_relat_1(A_536))
      | B_537 = A_536
      | k1_relat_1(B_537) != k1_relat_1(A_536)
      | ~ v1_funct_1(B_537)
      | ~ v1_relat_1(B_537)
      | ~ v1_funct_1(A_536)
      | ~ v1_relat_1(A_536) ) ),
    inference(resolution,[status(thm)],[c_5599,c_24])).

tff(c_6459,plain,(
    ! [B_537] :
      ( m1_subset_1('#skF_2'('#skF_6',B_537),'#skF_3')
      | B_537 = '#skF_6'
      | k1_relat_1(B_537) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_537)
      | ~ v1_relat_1(B_537)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5524,c_6450])).

tff(c_6558,plain,(
    ! [B_551] :
      ( m1_subset_1('#skF_2'('#skF_6',B_551),'#skF_3')
      | B_551 = '#skF_6'
      | k1_relat_1(B_551) != '#skF_3'
      | ~ v1_funct_1(B_551)
      | ~ v1_relat_1(B_551) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_66,c_5524,c_6459])).

tff(c_6841,plain,(
    ! [B_569] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_569)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_569))
      | B_569 = '#skF_6'
      | k1_relat_1(B_569) != '#skF_3'
      | ~ v1_funct_1(B_569)
      | ~ v1_relat_1(B_569) ) ),
    inference(resolution,[status(thm)],[c_6558,c_60])).

tff(c_6848,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6841,c_32])).

tff(c_6855,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_72,c_5534,c_210,c_66,c_5524,c_5534,c_6848])).

tff(c_6869,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6855,c_305])).

tff(c_6883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4986,c_6869])).

tff(c_6884,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5523])).

tff(c_6918,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6884,c_4986])).

tff(c_5001,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4993,c_4993,c_12])).

tff(c_6912,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6884,c_6884,c_5001])).

tff(c_4985,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_6976,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6912,c_4985])).

tff(c_6983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6918,c_6976])).

tff(c_6984,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5520])).

tff(c_7050,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6984,c_4986])).

tff(c_7044,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6984,c_6984,c_5001])).

tff(c_7072,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7044,c_4985])).

tff(c_7079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7050,c_7072])).

tff(c_7080,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_7081,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_7289,plain,
    ( v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7081,c_22])).

tff(c_7292,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7080,c_7289])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7213,plain,(
    ! [A_5] :
      ( A_5 = '#skF_6'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_7080,c_8])).

tff(c_7300,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7292,c_7213])).

tff(c_7306,plain,(
    ~ m1_subset_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7300,c_282])).

tff(c_300,plain,(
    ! [A_83] :
      ( m1_subset_1(A_83,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_283])).

tff(c_7417,plain,(
    ! [A_597] :
      ( m1_subset_1(A_597,'#skF_6')
      | ~ r2_hidden(A_597,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7300,c_300])).

tff(c_7425,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_7417])).

tff(c_7431,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_7425])).

tff(c_7434,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7431,c_22])).

tff(c_7437,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7080,c_7434])).

tff(c_7443,plain,(
    '#skF_1'('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7437,c_7213])).

tff(c_7477,plain,
    ( m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7443,c_124])).

tff(c_7487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_7306,c_7477])).

tff(c_7489,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_7495,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7489,c_113])).

tff(c_7502,plain,(
    ! [A_52] :
      ( A_52 = '#skF_5'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7495,c_113])).

tff(c_8164,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8158,c_7502])).

tff(c_8207,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8164,c_58])).

tff(c_8219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7609,c_8207])).

tff(c_8221,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_8157])).

tff(c_7639,plain,(
    ! [A_614,B_615,C_616] :
      ( k1_relset_1(A_614,B_615,C_616) = k1_relat_1(C_616)
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1(A_614,B_615))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7668,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_7639])).

tff(c_7921,plain,(
    ! [B_653,A_654,C_655] :
      ( B_653 = '#skF_5'
      | k1_relset_1(A_654,B_653,C_655) = A_654
      | ~ v1_funct_2(C_655,A_654,B_653)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_654,B_653))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7495,c_56])).

tff(c_7949,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_7921])).

tff(c_7962,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7668,c_7949])).

tff(c_7973,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7962])).

tff(c_7667,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_7639])).

tff(c_7946,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_7921])).

tff(c_7959,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7667,c_7946])).

tff(c_7963,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7959])).

tff(c_8261,plain,(
    ! [A_685,B_686] :
      ( r2_hidden('#skF_2'(A_685,B_686),k1_relat_1(A_685))
      | B_686 = A_685
      | k1_relat_1(B_686) != k1_relat_1(A_685)
      | ~ v1_funct_1(B_686)
      | ~ v1_relat_1(B_686)
      | ~ v1_funct_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9041,plain,(
    ! [A_722,B_723] :
      ( m1_subset_1('#skF_2'(A_722,B_723),k1_relat_1(A_722))
      | B_723 = A_722
      | k1_relat_1(B_723) != k1_relat_1(A_722)
      | ~ v1_funct_1(B_723)
      | ~ v1_relat_1(B_723)
      | ~ v1_funct_1(A_722)
      | ~ v1_relat_1(A_722) ) ),
    inference(resolution,[status(thm)],[c_8261,c_24])).

tff(c_9050,plain,(
    ! [B_723] :
      ( m1_subset_1('#skF_2'('#skF_6',B_723),'#skF_3')
      | B_723 = '#skF_6'
      | k1_relat_1(B_723) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_723)
      | ~ v1_relat_1(B_723)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7963,c_9041])).

tff(c_9278,plain,(
    ! [B_744] :
      ( m1_subset_1('#skF_2'('#skF_6',B_744),'#skF_3')
      | B_744 = '#skF_6'
      | k1_relat_1(B_744) != '#skF_3'
      | ~ v1_funct_1(B_744)
      | ~ v1_relat_1(B_744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_66,c_7963,c_9050])).

tff(c_9491,plain,(
    ! [B_764] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_764)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_764))
      | B_764 = '#skF_6'
      | k1_relat_1(B_764) != '#skF_3'
      | ~ v1_funct_1(B_764)
      | ~ v1_relat_1(B_764) ) ),
    inference(resolution,[status(thm)],[c_9278,c_60])).

tff(c_9498,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9491,c_32])).

tff(c_9505,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_72,c_7973,c_210,c_66,c_7963,c_7973,c_9498])).

tff(c_9568,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9505,c_7489])).

tff(c_9581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8221,c_9568])).

tff(c_9582,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7962])).

tff(c_9612,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9582,c_7489])).

tff(c_7503,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7495,c_7495,c_12])).

tff(c_9607,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9582,c_9582,c_7503])).

tff(c_7488,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_9637,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9607,c_7488])).

tff(c_9642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9612,c_9637])).

tff(c_9643,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7959])).

tff(c_9673,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9643,c_7489])).

tff(c_9668,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9643,c_9643,c_7503])).

tff(c_9697,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9668,c_7488])).

tff(c_9702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9673,c_9697])).

tff(c_9703,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_9704,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_9787,plain,
    ( v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_9704,c_22])).

tff(c_9790,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9703,c_9787])).

tff(c_9726,plain,(
    ! [A_769,C_770,B_771] :
      ( m1_subset_1(A_769,C_770)
      | ~ m1_subset_1(B_771,k1_zfmisc_1(C_770))
      | ~ r2_hidden(A_769,B_771) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9823,plain,(
    ! [A_776] :
      ( m1_subset_1(A_776,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_776,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_9726])).

tff(c_9826,plain,(
    ! [A_776] :
      ( v1_xboole_0(A_776)
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_776,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_9823,c_22])).

tff(c_9919,plain,(
    ! [A_781] :
      ( v1_xboole_0(A_781)
      | ~ r2_hidden(A_781,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9790,c_9826])).

tff(c_9929,plain,
    ( v1_xboole_0('#skF_1'('#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_9919])).

tff(c_9935,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9929])).

tff(c_9711,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_9703,c_8])).

tff(c_9941,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9935,c_9711])).

tff(c_9796,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9790,c_9711])).

tff(c_9948,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9941,c_9796])).

tff(c_9710,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9703,c_113])).

tff(c_9712,plain,(
    ! [B_8,A_7] :
      ( B_8 = '#skF_5'
      | A_7 = '#skF_5'
      | k2_zfmisc_1(A_7,B_8) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9710,c_9710,c_9710,c_10])).

tff(c_10178,plain,(
    ! [B_800,A_801] :
      ( B_800 = '#skF_6'
      | A_801 = '#skF_6'
      | k2_zfmisc_1(A_801,B_800) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9941,c_9941,c_9941,c_9712])).

tff(c_10192,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9948,c_10178])).

tff(c_10220,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10192])).

tff(c_10241,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10220,c_9935])).

tff(c_10247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_10241])).

tff(c_10248,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10192])).

tff(c_9854,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9796,c_62])).

tff(c_9945,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9941,c_9854])).

tff(c_10262,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10248,c_10248,c_9945])).

tff(c_10269,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10248,c_9941])).

tff(c_9718,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9710,c_9710,c_12])).

tff(c_9877,plain,(
    ! [A_777,B_778,D_779] :
      ( r2_relset_1(A_777,B_778,D_779,D_779)
      | ~ m1_subset_1(D_779,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9881,plain,(
    ! [A_7,D_779] :
      ( r2_relset_1(A_7,'#skF_5',D_779,D_779)
      | ~ m1_subset_1(D_779,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9718,c_9877])).

tff(c_10561,plain,(
    ! [A_837,D_838] :
      ( r2_relset_1(A_837,'#skF_4',D_838,D_838)
      | ~ m1_subset_1(D_838,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10269,c_10269,c_9881])).

tff(c_10577,plain,(
    ! [A_837] : r2_relset_1(A_837,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_10262,c_10561])).

tff(c_9960,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9941,c_58])).

tff(c_10264,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10248,c_10248,c_9960])).

tff(c_10587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10577,c_10264])).

tff(c_10589,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9929])).

tff(c_9853,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9796,c_173])).

tff(c_10588,plain,(
    v1_xboole_0('#skF_1'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_9929])).

tff(c_10595,plain,(
    '#skF_1'('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10588,c_9711])).

tff(c_105,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,A_50)
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_10605,plain,
    ( ~ r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10595,c_109])).

tff(c_10613,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9853,c_10605])).

tff(c_10615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10589,c_10613])).

tff(c_10617,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_10623,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10617,c_113])).

tff(c_46,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_10692,plain,(
    ! [A_36] :
      ( v1_funct_2('#skF_3',A_36,'#skF_3')
      | A_36 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10623,c_10623,c_10623,c_10623,c_10623,c_76])).

tff(c_10693,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10692])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10643,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10623,c_10623,c_14])).

tff(c_10672,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_68])).

tff(c_10738,plain,(
    ! [A_847,C_848,B_849] :
      ( m1_subset_1(A_847,C_848)
      | ~ m1_subset_1(B_849,k1_zfmisc_1(C_848))
      | ~ r2_hidden(A_847,B_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10788,plain,(
    ! [A_851] :
      ( m1_subset_1(A_851,'#skF_3')
      | ~ r2_hidden(A_851,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10672,c_10738])).

tff(c_10798,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_10788])).

tff(c_10810,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10798])).

tff(c_10624,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_10617,c_8])).

tff(c_10820,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10810,c_10624])).

tff(c_10826,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10820,c_10672])).

tff(c_10835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10693,c_10826])).

tff(c_10837,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10798])).

tff(c_10669,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_174])).

tff(c_10836,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_10798])).

tff(c_10857,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10836,c_22])).

tff(c_10863,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10617,c_10857])).

tff(c_10874,plain,(
    '#skF_1'('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10863,c_10624])).

tff(c_10891,plain,
    ( ~ r1_tarski('#skF_5','#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10874,c_109])).

tff(c_10899,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10669,c_10891])).

tff(c_10901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10837,c_10899])).

tff(c_10903,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10692])).

tff(c_11012,plain,(
    ! [A_863,B_864,D_865] :
      ( r2_relset_1(A_863,B_864,D_865,D_865)
      | ~ m1_subset_1(D_865,k1_zfmisc_1(k2_zfmisc_1(A_863,B_864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_11295,plain,(
    ! [B_895,D_896] :
      ( r2_relset_1('#skF_3',B_895,D_896,D_896)
      | ~ m1_subset_1(D_896,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10643,c_11012])).

tff(c_11311,plain,(
    ! [B_895] : r2_relset_1('#skF_3',B_895,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10903,c_11295])).

tff(c_10671,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_62])).

tff(c_10931,plain,(
    ! [A_856,C_857,B_858] :
      ( m1_subset_1(A_856,C_857)
      | ~ m1_subset_1(B_858,k1_zfmisc_1(C_857))
      | ~ r2_hidden(A_856,B_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_11029,plain,(
    ! [A_866] :
      ( m1_subset_1(A_866,'#skF_3')
      | ~ r2_hidden(A_866,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10671,c_10931])).

tff(c_11039,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_11029])).

tff(c_11103,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11039])).

tff(c_11123,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11103,c_10624])).

tff(c_10967,plain,(
    ! [A_860] :
      ( m1_subset_1(A_860,'#skF_3')
      | ~ r2_hidden(A_860,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10672,c_10931])).

tff(c_10977,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_10967])).

tff(c_11040,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10977])).

tff(c_11055,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11040,c_10624])).

tff(c_11064,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11055,c_58])).

tff(c_11128,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11123,c_11064])).

tff(c_11319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11311,c_11128])).

tff(c_11321,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_11039])).

tff(c_10670,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_173])).

tff(c_11320,plain,(
    m1_subset_1('#skF_1'('#skF_6'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_11039])).

tff(c_11324,plain,
    ( v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_11320,c_22])).

tff(c_11327,plain,(
    v1_xboole_0('#skF_1'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10617,c_11324])).

tff(c_11341,plain,(
    '#skF_1'('#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11327,c_10624])).

tff(c_11352,plain,
    ( ~ r1_tarski('#skF_6','#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11341,c_109])).

tff(c_11360,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10670,c_11352])).

tff(c_11362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11321,c_11360])).

tff(c_11364,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10977])).

tff(c_11363,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_10977])).

tff(c_11372,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_11363,c_22])).

tff(c_11378,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10617,c_11372])).

tff(c_11389,plain,(
    '#skF_1'('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11378,c_10624])).

tff(c_11400,plain,
    ( ~ r1_tarski('#skF_5','#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11389,c_109])).

tff(c_11408,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10669,c_11400])).

tff(c_11410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11364,c_11408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.31/3.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/3.88  
% 10.40/3.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/3.89  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 10.40/3.89  
% 10.40/3.89  %Foreground sorts:
% 10.40/3.89  
% 10.40/3.89  
% 10.40/3.89  %Background operators:
% 10.40/3.89  
% 10.40/3.89  
% 10.40/3.89  %Foreground operators:
% 10.40/3.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.40/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.40/3.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.40/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.40/3.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.40/3.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.40/3.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.40/3.89  tff('#skF_5', type, '#skF_5': $i).
% 10.40/3.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.40/3.89  tff('#skF_6', type, '#skF_6': $i).
% 10.40/3.89  tff('#skF_3', type, '#skF_3': $i).
% 10.40/3.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.40/3.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.40/3.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.40/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.40/3.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.40/3.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.40/3.89  tff('#skF_4', type, '#skF_4': $i).
% 10.40/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.40/3.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.40/3.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.40/3.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.40/3.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.40/3.89  
% 10.40/3.92  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.40/3.92  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 10.40/3.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.40/3.92  tff(f_112, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.40/3.92  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.40/3.92  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 10.40/3.92  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.40/3.92  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.40/3.92  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.40/3.92  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.40/3.92  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 10.40/3.92  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.40/3.92  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.40/3.92  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.40/3.92  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 10.40/3.92  tff(c_20, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~v1_xboole_0(B_10) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.40/3.92  tff(c_128, plain, (![E_60]: (k1_funct_1('#skF_5', E_60)=k1_funct_1('#skF_6', E_60) | ~m1_subset_1(E_60, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_137, plain, (![B_10]: (k1_funct_1('#skF_5', B_10)=k1_funct_1('#skF_6', B_10) | ~v1_xboole_0(B_10) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_128])).
% 10.40/3.92  tff(c_260, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_137])).
% 10.40/3.92  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.40/3.92  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_7588, plain, (![A_608, B_609, D_610]: (r2_relset_1(A_608, B_609, D_610, D_610) | ~m1_subset_1(D_610, k1_zfmisc_1(k2_zfmisc_1(A_608, B_609))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.92  tff(c_7609, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_7588])).
% 10.40/3.92  tff(c_156, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.40/3.92  tff(c_173, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_156])).
% 10.40/3.92  tff(c_18, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.40/3.92  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.40/3.92  tff(c_283, plain, (![A_83, C_84, B_85]: (m1_subset_1(A_83, C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/3.92  tff(c_7694, plain, (![A_621, B_622, A_623]: (m1_subset_1(A_621, B_622) | ~r2_hidden(A_621, A_623) | ~r1_tarski(A_623, B_622))), inference(resolution, [status(thm)], [c_28, c_283])).
% 10.40/3.92  tff(c_8144, plain, (![B_674, B_675, A_676]: (m1_subset_1(B_674, B_675) | ~r1_tarski(A_676, B_675) | ~m1_subset_1(B_674, A_676) | v1_xboole_0(A_676))), inference(resolution, [status(thm)], [c_18, c_7694])).
% 10.40/3.92  tff(c_8157, plain, (![B_674]: (m1_subset_1(B_674, k2_zfmisc_1('#skF_3', '#skF_4')) | ~m1_subset_1(B_674, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_173, c_8144])).
% 10.40/3.92  tff(c_8158, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_8157])).
% 10.40/3.92  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_174, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_156])).
% 10.40/3.92  tff(c_245, plain, (![B_75, A_76]: (r2_hidden(B_75, A_76) | ~m1_subset_1(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.40/3.92  tff(c_36, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.40/3.92  tff(c_273, plain, (![A_81, B_82]: (~r1_tarski(A_81, B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_245, c_36])).
% 10.40/3.92  tff(c_280, plain, (~m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_174, c_273])).
% 10.40/3.92  tff(c_282, plain, (~m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_280])).
% 10.40/3.92  tff(c_304, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_20, c_282])).
% 10.40/3.92  tff(c_305, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_304])).
% 10.40/3.92  tff(c_281, plain, (~m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_173, c_273])).
% 10.40/3.92  tff(c_311, plain, (~m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_281])).
% 10.40/3.92  tff(c_315, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_20, c_311])).
% 10.40/3.92  tff(c_316, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_315])).
% 10.40/3.92  tff(c_2739, plain, (![A_260, B_261, D_262]: (r2_relset_1(A_260, B_261, D_262, D_262) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.92  tff(c_2760, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_2739])).
% 10.40/3.92  tff(c_184, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.92  tff(c_211, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_184])).
% 10.40/3.92  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_2888, plain, (![A_285, B_286, C_287]: (k1_relset_1(A_285, B_286, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.92  tff(c_2924, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_2888])).
% 10.40/3.92  tff(c_3107, plain, (![B_305, A_306, C_307]: (k1_xboole_0=B_305 | k1_relset_1(A_306, B_305, C_307)=A_306 | ~v1_funct_2(C_307, A_306, B_305) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_306, B_305))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.40/3.92  tff(c_3129, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_3107])).
% 10.40/3.92  tff(c_3147, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2924, c_3129])).
% 10.40/3.92  tff(c_3155, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3147])).
% 10.40/3.92  tff(c_210, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_184])).
% 10.40/3.92  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_2923, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_2888])).
% 10.40/3.92  tff(c_3126, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_3107])).
% 10.40/3.92  tff(c_3144, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2923, c_3126])).
% 10.40/3.92  tff(c_3149, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_3144])).
% 10.40/3.92  tff(c_3370, plain, (![A_329, B_330]: (r2_hidden('#skF_2'(A_329, B_330), k1_relat_1(A_329)) | B_330=A_329 | k1_relat_1(B_330)!=k1_relat_1(A_329) | ~v1_funct_1(B_330) | ~v1_relat_1(B_330) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.40/3.92  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.40/3.92  tff(c_3983, plain, (![A_371, B_372]: (m1_subset_1('#skF_2'(A_371, B_372), k1_relat_1(A_371)) | B_372=A_371 | k1_relat_1(B_372)!=k1_relat_1(A_371) | ~v1_funct_1(B_372) | ~v1_relat_1(B_372) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(resolution, [status(thm)], [c_3370, c_24])).
% 10.40/3.92  tff(c_3992, plain, (![B_372]: (m1_subset_1('#skF_2'('#skF_6', B_372), '#skF_3') | B_372='#skF_6' | k1_relat_1(B_372)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_372) | ~v1_relat_1(B_372) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3149, c_3983])).
% 10.40/3.92  tff(c_4257, plain, (![B_390]: (m1_subset_1('#skF_2'('#skF_6', B_390), '#skF_3') | B_390='#skF_6' | k1_relat_1(B_390)!='#skF_3' | ~v1_funct_1(B_390) | ~v1_relat_1(B_390))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_66, c_3149, c_3992])).
% 10.40/3.92  tff(c_60, plain, (![E_43]: (k1_funct_1('#skF_5', E_43)=k1_funct_1('#skF_6', E_43) | ~m1_subset_1(E_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_4285, plain, (![B_395]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_395))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_395)) | B_395='#skF_6' | k1_relat_1(B_395)!='#skF_3' | ~v1_funct_1(B_395) | ~v1_relat_1(B_395))), inference(resolution, [status(thm)], [c_4257, c_60])).
% 10.40/3.92  tff(c_32, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_2'(A_18, B_22))!=k1_funct_1(A_18, '#skF_2'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.40/3.92  tff(c_4292, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4285, c_32])).
% 10.40/3.92  tff(c_4299, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_72, c_3155, c_210, c_66, c_3155, c_3149, c_4292])).
% 10.40/3.92  tff(c_58, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.40/3.92  tff(c_4317, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4299, c_58])).
% 10.40/3.92  tff(c_4328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2760, c_4317])).
% 10.40/3.92  tff(c_4329, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3147])).
% 10.40/3.92  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.40/3.92  tff(c_4363, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_6])).
% 10.40/3.92  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.40/3.92  tff(c_4361, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_4329, c_12])).
% 10.40/3.92  tff(c_306, plain, (![A_86]: (m1_subset_1(A_86, k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_86, '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_283])).
% 10.40/3.92  tff(c_22, plain, (![B_10, A_9]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.40/3.92  tff(c_310, plain, (![A_86]: (v1_xboole_0(A_86) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_86, '#skF_6'))), inference(resolution, [status(thm)], [c_306, c_22])).
% 10.40/3.92  tff(c_2819, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_310])).
% 10.40/3.92  tff(c_4424, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4361, c_2819])).
% 10.40/3.92  tff(c_4435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4424])).
% 10.40/3.92  tff(c_4436, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3144])).
% 10.40/3.92  tff(c_4470, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4436, c_6])).
% 10.40/3.92  tff(c_4468, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4436, c_4436, c_12])).
% 10.40/3.92  tff(c_4522, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4468, c_2819])).
% 10.40/3.92  tff(c_4533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4470, c_4522])).
% 10.40/3.92  tff(c_4535, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_310])).
% 10.40/3.92  tff(c_110, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.40/3.92  tff(c_113, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_6, c_110])).
% 10.40/3.92  tff(c_4541, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4535, c_113])).
% 10.40/3.92  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.40/3.92  tff(c_4567, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4541, c_10])).
% 10.40/3.92  tff(c_4678, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4567])).
% 10.40/3.92  tff(c_4705, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4678, c_6])).
% 10.40/3.92  tff(c_4707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_4705])).
% 10.40/3.92  tff(c_4708, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4567])).
% 10.40/3.92  tff(c_4545, plain, (~m1_subset_1(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4541, c_311])).
% 10.40/3.92  tff(c_4722, plain, (~m1_subset_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4708, c_4545])).
% 10.40/3.92  tff(c_4947, plain, (![A_417]: (v1_xboole_0(A_417) | ~r2_hidden(A_417, '#skF_6'))), inference(splitRight, [status(thm)], [c_310])).
% 10.40/3.92  tff(c_4955, plain, (v1_xboole_0('#skF_1'('#skF_6')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_4947])).
% 10.40/3.92  tff(c_4961, plain, (v1_xboole_0('#skF_1'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_316, c_4955])).
% 10.40/3.92  tff(c_4742, plain, (![A_52]: (A_52='#skF_4' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_4708, c_113])).
% 10.40/3.92  tff(c_4967, plain, ('#skF_1'('#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_4961, c_4742])).
% 10.40/3.92  tff(c_120, plain, (![A_54, B_55]: (m1_subset_1(A_54, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.40/3.92  tff(c_124, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_120])).
% 10.40/3.92  tff(c_4974, plain, (m1_subset_1('#skF_4', '#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4967, c_124])).
% 10.40/3.92  tff(c_4984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_4722, c_4974])).
% 10.40/3.92  tff(c_4986, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_315])).
% 10.40/3.92  tff(c_5103, plain, (![A_427, B_428, C_429]: (k1_relset_1(A_427, B_428, C_429)=k1_relat_1(C_429) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.92  tff(c_5132, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_5103])).
% 10.40/3.92  tff(c_4993, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_4986, c_113])).
% 10.40/3.92  tff(c_56, plain, (![B_37, A_36, C_38]: (k1_xboole_0=B_37 | k1_relset_1(A_36, B_37, C_38)=A_36 | ~v1_funct_2(C_38, A_36, B_37) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.40/3.92  tff(c_5482, plain, (![B_478, A_479, C_480]: (B_478='#skF_6' | k1_relset_1(A_479, B_478, C_480)=A_479 | ~v1_funct_2(C_480, A_479, B_478) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_479, B_478))))), inference(demodulation, [status(thm), theory('equality')], [c_4993, c_56])).
% 10.40/3.92  tff(c_5510, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_5482])).
% 10.40/3.92  tff(c_5523, plain, ('#skF_6'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5132, c_5510])).
% 10.40/3.92  tff(c_5534, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5523])).
% 10.40/3.92  tff(c_5131, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_5103])).
% 10.40/3.92  tff(c_5507, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_5482])).
% 10.40/3.92  tff(c_5520, plain, ('#skF_6'='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5131, c_5507])).
% 10.40/3.92  tff(c_5524, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_5520])).
% 10.40/3.92  tff(c_5599, plain, (![A_487, B_488]: (r2_hidden('#skF_2'(A_487, B_488), k1_relat_1(A_487)) | B_488=A_487 | k1_relat_1(B_488)!=k1_relat_1(A_487) | ~v1_funct_1(B_488) | ~v1_relat_1(B_488) | ~v1_funct_1(A_487) | ~v1_relat_1(A_487))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.40/3.92  tff(c_6450, plain, (![A_536, B_537]: (m1_subset_1('#skF_2'(A_536, B_537), k1_relat_1(A_536)) | B_537=A_536 | k1_relat_1(B_537)!=k1_relat_1(A_536) | ~v1_funct_1(B_537) | ~v1_relat_1(B_537) | ~v1_funct_1(A_536) | ~v1_relat_1(A_536))), inference(resolution, [status(thm)], [c_5599, c_24])).
% 10.40/3.92  tff(c_6459, plain, (![B_537]: (m1_subset_1('#skF_2'('#skF_6', B_537), '#skF_3') | B_537='#skF_6' | k1_relat_1(B_537)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_537) | ~v1_relat_1(B_537) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5524, c_6450])).
% 10.40/3.92  tff(c_6558, plain, (![B_551]: (m1_subset_1('#skF_2'('#skF_6', B_551), '#skF_3') | B_551='#skF_6' | k1_relat_1(B_551)!='#skF_3' | ~v1_funct_1(B_551) | ~v1_relat_1(B_551))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_66, c_5524, c_6459])).
% 10.40/3.92  tff(c_6841, plain, (![B_569]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_569))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_569)) | B_569='#skF_6' | k1_relat_1(B_569)!='#skF_3' | ~v1_funct_1(B_569) | ~v1_relat_1(B_569))), inference(resolution, [status(thm)], [c_6558, c_60])).
% 10.40/3.92  tff(c_6848, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6841, c_32])).
% 10.40/3.92  tff(c_6855, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_72, c_5534, c_210, c_66, c_5524, c_5534, c_6848])).
% 10.40/3.92  tff(c_6869, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6855, c_305])).
% 10.40/3.92  tff(c_6883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4986, c_6869])).
% 10.40/3.92  tff(c_6884, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_5523])).
% 10.40/3.92  tff(c_6918, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6884, c_4986])).
% 10.40/3.92  tff(c_5001, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4993, c_4993, c_12])).
% 10.40/3.92  tff(c_6912, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6884, c_6884, c_5001])).
% 10.40/3.92  tff(c_4985, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_315])).
% 10.40/3.92  tff(c_6976, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6912, c_4985])).
% 10.40/3.92  tff(c_6983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6918, c_6976])).
% 10.40/3.92  tff(c_6984, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_5520])).
% 10.40/3.92  tff(c_7050, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6984, c_4986])).
% 10.40/3.92  tff(c_7044, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6984, c_6984, c_5001])).
% 10.40/3.92  tff(c_7072, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7044, c_4985])).
% 10.40/3.92  tff(c_7079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7050, c_7072])).
% 10.40/3.92  tff(c_7080, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_281])).
% 10.40/3.92  tff(c_7081, plain, (m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_281])).
% 10.40/3.92  tff(c_7289, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7081, c_22])).
% 10.40/3.92  tff(c_7292, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7080, c_7289])).
% 10.40/3.92  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.40/3.92  tff(c_7213, plain, (![A_5]: (A_5='#skF_6' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_7080, c_8])).
% 10.40/3.92  tff(c_7300, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_7292, c_7213])).
% 10.40/3.92  tff(c_7306, plain, (~m1_subset_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7300, c_282])).
% 10.40/3.92  tff(c_300, plain, (![A_83]: (m1_subset_1(A_83, k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_283])).
% 10.40/3.92  tff(c_7417, plain, (![A_597]: (m1_subset_1(A_597, '#skF_6') | ~r2_hidden(A_597, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7300, c_300])).
% 10.40/3.92  tff(c_7425, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_7417])).
% 10.40/3.92  tff(c_7431, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_305, c_7425])).
% 10.40/3.92  tff(c_7434, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7431, c_22])).
% 10.40/3.92  tff(c_7437, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7080, c_7434])).
% 10.40/3.92  tff(c_7443, plain, ('#skF_1'('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_7437, c_7213])).
% 10.40/3.92  tff(c_7477, plain, (m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7443, c_124])).
% 10.40/3.92  tff(c_7487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_7306, c_7477])).
% 10.40/3.92  tff(c_7489, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_304])).
% 10.40/3.92  tff(c_7495, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7489, c_113])).
% 10.40/3.92  tff(c_7502, plain, (![A_52]: (A_52='#skF_5' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_7495, c_113])).
% 10.40/3.92  tff(c_8164, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_8158, c_7502])).
% 10.40/3.92  tff(c_8207, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8164, c_58])).
% 10.40/3.92  tff(c_8219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7609, c_8207])).
% 10.40/3.92  tff(c_8221, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_8157])).
% 10.40/3.92  tff(c_7639, plain, (![A_614, B_615, C_616]: (k1_relset_1(A_614, B_615, C_616)=k1_relat_1(C_616) | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1(A_614, B_615))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.92  tff(c_7668, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_7639])).
% 10.40/3.92  tff(c_7921, plain, (![B_653, A_654, C_655]: (B_653='#skF_5' | k1_relset_1(A_654, B_653, C_655)=A_654 | ~v1_funct_2(C_655, A_654, B_653) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_654, B_653))))), inference(demodulation, [status(thm), theory('equality')], [c_7495, c_56])).
% 10.40/3.92  tff(c_7949, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_7921])).
% 10.40/3.92  tff(c_7962, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7668, c_7949])).
% 10.40/3.92  tff(c_7973, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_7962])).
% 10.40/3.92  tff(c_7667, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_7639])).
% 10.40/3.92  tff(c_7946, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_7921])).
% 10.40/3.92  tff(c_7959, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_7667, c_7946])).
% 10.40/3.92  tff(c_7963, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_7959])).
% 10.40/3.92  tff(c_8261, plain, (![A_685, B_686]: (r2_hidden('#skF_2'(A_685, B_686), k1_relat_1(A_685)) | B_686=A_685 | k1_relat_1(B_686)!=k1_relat_1(A_685) | ~v1_funct_1(B_686) | ~v1_relat_1(B_686) | ~v1_funct_1(A_685) | ~v1_relat_1(A_685))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.40/3.92  tff(c_9041, plain, (![A_722, B_723]: (m1_subset_1('#skF_2'(A_722, B_723), k1_relat_1(A_722)) | B_723=A_722 | k1_relat_1(B_723)!=k1_relat_1(A_722) | ~v1_funct_1(B_723) | ~v1_relat_1(B_723) | ~v1_funct_1(A_722) | ~v1_relat_1(A_722))), inference(resolution, [status(thm)], [c_8261, c_24])).
% 10.40/3.92  tff(c_9050, plain, (![B_723]: (m1_subset_1('#skF_2'('#skF_6', B_723), '#skF_3') | B_723='#skF_6' | k1_relat_1(B_723)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_723) | ~v1_relat_1(B_723) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7963, c_9041])).
% 10.40/3.92  tff(c_9278, plain, (![B_744]: (m1_subset_1('#skF_2'('#skF_6', B_744), '#skF_3') | B_744='#skF_6' | k1_relat_1(B_744)!='#skF_3' | ~v1_funct_1(B_744) | ~v1_relat_1(B_744))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_66, c_7963, c_9050])).
% 10.40/3.92  tff(c_9491, plain, (![B_764]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_764))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_764)) | B_764='#skF_6' | k1_relat_1(B_764)!='#skF_3' | ~v1_funct_1(B_764) | ~v1_relat_1(B_764))), inference(resolution, [status(thm)], [c_9278, c_60])).
% 10.40/3.92  tff(c_9498, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9491, c_32])).
% 10.40/3.92  tff(c_9505, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_72, c_7973, c_210, c_66, c_7963, c_7973, c_9498])).
% 10.40/3.92  tff(c_9568, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9505, c_7489])).
% 10.40/3.92  tff(c_9581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8221, c_9568])).
% 10.40/3.92  tff(c_9582, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_7962])).
% 10.40/3.92  tff(c_9612, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9582, c_7489])).
% 10.40/3.92  tff(c_7503, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7495, c_7495, c_12])).
% 10.40/3.92  tff(c_9607, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9582, c_9582, c_7503])).
% 10.40/3.92  tff(c_7488, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_304])).
% 10.40/3.92  tff(c_9637, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9607, c_7488])).
% 10.40/3.92  tff(c_9642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9612, c_9637])).
% 10.40/3.92  tff(c_9643, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_7959])).
% 10.40/3.92  tff(c_9673, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9643, c_7489])).
% 10.40/3.92  tff(c_9668, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9643, c_9643, c_7503])).
% 10.40/3.92  tff(c_9697, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9668, c_7488])).
% 10.40/3.92  tff(c_9702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9673, c_9697])).
% 10.40/3.92  tff(c_9703, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_280])).
% 10.40/3.92  tff(c_9704, plain, (m1_subset_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_280])).
% 10.40/3.92  tff(c_9787, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_9704, c_22])).
% 10.40/3.92  tff(c_9790, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9703, c_9787])).
% 10.40/3.92  tff(c_9726, plain, (![A_769, C_770, B_771]: (m1_subset_1(A_769, C_770) | ~m1_subset_1(B_771, k1_zfmisc_1(C_770)) | ~r2_hidden(A_769, B_771))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/3.92  tff(c_9823, plain, (![A_776]: (m1_subset_1(A_776, k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_776, '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_9726])).
% 10.40/3.92  tff(c_9826, plain, (![A_776]: (v1_xboole_0(A_776) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_776, '#skF_6'))), inference(resolution, [status(thm)], [c_9823, c_22])).
% 10.40/3.92  tff(c_9919, plain, (![A_781]: (v1_xboole_0(A_781) | ~r2_hidden(A_781, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9790, c_9826])).
% 10.40/3.92  tff(c_9929, plain, (v1_xboole_0('#skF_1'('#skF_6')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_9919])).
% 10.40/3.92  tff(c_9935, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9929])).
% 10.40/3.92  tff(c_9711, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_9703, c_8])).
% 10.40/3.92  tff(c_9941, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_9935, c_9711])).
% 10.40/3.92  tff(c_9796, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_9790, c_9711])).
% 10.40/3.92  tff(c_9948, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9941, c_9796])).
% 10.40/3.92  tff(c_9710, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_9703, c_113])).
% 10.40/3.92  tff(c_9712, plain, (![B_8, A_7]: (B_8='#skF_5' | A_7='#skF_5' | k2_zfmisc_1(A_7, B_8)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9710, c_9710, c_9710, c_10])).
% 10.40/3.92  tff(c_10178, plain, (![B_800, A_801]: (B_800='#skF_6' | A_801='#skF_6' | k2_zfmisc_1(A_801, B_800)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9941, c_9941, c_9941, c_9712])).
% 10.40/3.92  tff(c_10192, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9948, c_10178])).
% 10.40/3.92  tff(c_10220, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_10192])).
% 10.40/3.92  tff(c_10241, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10220, c_9935])).
% 10.40/3.92  tff(c_10247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_10241])).
% 10.40/3.92  tff(c_10248, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_10192])).
% 10.40/3.92  tff(c_9854, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9796, c_62])).
% 10.40/3.92  tff(c_9945, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9941, c_9854])).
% 10.40/3.92  tff(c_10262, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10248, c_10248, c_9945])).
% 10.40/3.92  tff(c_10269, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10248, c_9941])).
% 10.40/3.92  tff(c_9718, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9710, c_9710, c_12])).
% 10.40/3.92  tff(c_9877, plain, (![A_777, B_778, D_779]: (r2_relset_1(A_777, B_778, D_779, D_779) | ~m1_subset_1(D_779, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.92  tff(c_9881, plain, (![A_7, D_779]: (r2_relset_1(A_7, '#skF_5', D_779, D_779) | ~m1_subset_1(D_779, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9718, c_9877])).
% 10.40/3.92  tff(c_10561, plain, (![A_837, D_838]: (r2_relset_1(A_837, '#skF_4', D_838, D_838) | ~m1_subset_1(D_838, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10269, c_10269, c_9881])).
% 10.40/3.92  tff(c_10577, plain, (![A_837]: (r2_relset_1(A_837, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_10262, c_10561])).
% 10.40/3.92  tff(c_9960, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9941, c_58])).
% 10.40/3.92  tff(c_10264, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10248, c_10248, c_9960])).
% 10.40/3.92  tff(c_10587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10577, c_10264])).
% 10.40/3.92  tff(c_10589, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_9929])).
% 10.40/3.92  tff(c_9853, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9796, c_173])).
% 10.40/3.92  tff(c_10588, plain, (v1_xboole_0('#skF_1'('#skF_6'))), inference(splitRight, [status(thm)], [c_9929])).
% 10.40/3.92  tff(c_10595, plain, ('#skF_1'('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_10588, c_9711])).
% 10.40/3.92  tff(c_105, plain, (![B_49, A_50]: (~r1_tarski(B_49, A_50) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.40/3.92  tff(c_109, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_105])).
% 10.40/3.92  tff(c_10605, plain, (~r1_tarski('#skF_6', '#skF_5') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10595, c_109])).
% 10.40/3.92  tff(c_10613, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9853, c_10605])).
% 10.40/3.92  tff(c_10615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10589, c_10613])).
% 10.40/3.92  tff(c_10617, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 10.40/3.92  tff(c_10623, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10617, c_113])).
% 10.40/3.92  tff(c_46, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.40/3.92  tff(c_76, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 10.40/3.92  tff(c_10692, plain, (![A_36]: (v1_funct_2('#skF_3', A_36, '#skF_3') | A_36='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10623, c_10623, c_10623, c_10623, c_10623, c_76])).
% 10.40/3.92  tff(c_10693, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10692])).
% 10.40/3.92  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.40/3.92  tff(c_10643, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10623, c_10623, c_14])).
% 10.40/3.92  tff(c_10672, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_68])).
% 10.40/3.92  tff(c_10738, plain, (![A_847, C_848, B_849]: (m1_subset_1(A_847, C_848) | ~m1_subset_1(B_849, k1_zfmisc_1(C_848)) | ~r2_hidden(A_847, B_849))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/3.92  tff(c_10788, plain, (![A_851]: (m1_subset_1(A_851, '#skF_3') | ~r2_hidden(A_851, '#skF_5'))), inference(resolution, [status(thm)], [c_10672, c_10738])).
% 10.40/3.92  tff(c_10798, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_10788])).
% 10.40/3.92  tff(c_10810, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_10798])).
% 10.40/3.92  tff(c_10624, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_10617, c_8])).
% 10.40/3.92  tff(c_10820, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_10810, c_10624])).
% 10.40/3.92  tff(c_10826, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10820, c_10672])).
% 10.40/3.92  tff(c_10835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10693, c_10826])).
% 10.40/3.92  tff(c_10837, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_10798])).
% 10.40/3.92  tff(c_10669, plain, (r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_174])).
% 10.40/3.92  tff(c_10836, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_10798])).
% 10.40/3.92  tff(c_10857, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10836, c_22])).
% 10.40/3.92  tff(c_10863, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10617, c_10857])).
% 10.40/3.92  tff(c_10874, plain, ('#skF_1'('#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_10863, c_10624])).
% 10.40/3.92  tff(c_10891, plain, (~r1_tarski('#skF_5', '#skF_3') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10874, c_109])).
% 10.40/3.92  tff(c_10899, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10669, c_10891])).
% 10.40/3.92  tff(c_10901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10837, c_10899])).
% 10.40/3.92  tff(c_10903, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10692])).
% 10.40/3.92  tff(c_11012, plain, (![A_863, B_864, D_865]: (r2_relset_1(A_863, B_864, D_865, D_865) | ~m1_subset_1(D_865, k1_zfmisc_1(k2_zfmisc_1(A_863, B_864))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.92  tff(c_11295, plain, (![B_895, D_896]: (r2_relset_1('#skF_3', B_895, D_896, D_896) | ~m1_subset_1(D_896, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10643, c_11012])).
% 10.40/3.92  tff(c_11311, plain, (![B_895]: (r2_relset_1('#skF_3', B_895, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_10903, c_11295])).
% 10.40/3.92  tff(c_10671, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_62])).
% 10.40/3.92  tff(c_10931, plain, (![A_856, C_857, B_858]: (m1_subset_1(A_856, C_857) | ~m1_subset_1(B_858, k1_zfmisc_1(C_857)) | ~r2_hidden(A_856, B_858))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.40/3.92  tff(c_11029, plain, (![A_866]: (m1_subset_1(A_866, '#skF_3') | ~r2_hidden(A_866, '#skF_6'))), inference(resolution, [status(thm)], [c_10671, c_10931])).
% 10.40/3.92  tff(c_11039, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_3') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_11029])).
% 10.40/3.92  tff(c_11103, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_11039])).
% 10.40/3.92  tff(c_11123, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_11103, c_10624])).
% 10.40/3.92  tff(c_10967, plain, (![A_860]: (m1_subset_1(A_860, '#skF_3') | ~r2_hidden(A_860, '#skF_5'))), inference(resolution, [status(thm)], [c_10672, c_10931])).
% 10.40/3.92  tff(c_10977, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_10967])).
% 10.40/3.92  tff(c_11040, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_10977])).
% 10.40/3.92  tff(c_11055, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_11040, c_10624])).
% 10.40/3.92  tff(c_11064, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11055, c_58])).
% 10.40/3.92  tff(c_11128, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11123, c_11064])).
% 10.40/3.92  tff(c_11319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11311, c_11128])).
% 10.40/3.92  tff(c_11321, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_11039])).
% 10.40/3.92  tff(c_10670, plain, (r1_tarski('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_173])).
% 10.40/3.92  tff(c_11320, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_3')), inference(splitRight, [status(thm)], [c_11039])).
% 10.40/3.92  tff(c_11324, plain, (v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_11320, c_22])).
% 10.40/3.92  tff(c_11327, plain, (v1_xboole_0('#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10617, c_11324])).
% 10.40/3.92  tff(c_11341, plain, ('#skF_1'('#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_11327, c_10624])).
% 10.40/3.92  tff(c_11352, plain, (~r1_tarski('#skF_6', '#skF_3') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11341, c_109])).
% 10.40/3.92  tff(c_11360, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10670, c_11352])).
% 10.40/3.92  tff(c_11362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11321, c_11360])).
% 10.40/3.92  tff(c_11364, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_10977])).
% 10.40/3.92  tff(c_11363, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_10977])).
% 10.40/3.92  tff(c_11372, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_11363, c_22])).
% 10.40/3.92  tff(c_11378, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10617, c_11372])).
% 10.40/3.92  tff(c_11389, plain, ('#skF_1'('#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_11378, c_10624])).
% 10.40/3.92  tff(c_11400, plain, (~r1_tarski('#skF_5', '#skF_3') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11389, c_109])).
% 10.40/3.92  tff(c_11408, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10669, c_11400])).
% 10.40/3.92  tff(c_11410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11364, c_11408])).
% 10.40/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/3.92  
% 10.40/3.92  Inference rules
% 10.40/3.92  ----------------------
% 10.40/3.92  #Ref     : 5
% 10.40/3.92  #Sup     : 2370
% 10.40/3.92  #Fact    : 0
% 10.40/3.92  #Define  : 0
% 10.40/3.92  #Split   : 62
% 10.40/3.92  #Chain   : 0
% 10.40/3.92  #Close   : 0
% 10.40/3.92  
% 10.40/3.92  Ordering : KBO
% 10.40/3.92  
% 10.40/3.92  Simplification rules
% 10.40/3.92  ----------------------
% 10.40/3.92  #Subsume      : 486
% 10.40/3.92  #Demod        : 2625
% 10.40/3.92  #Tautology    : 969
% 10.40/3.92  #SimpNegUnit  : 322
% 10.40/3.92  #BackRed      : 858
% 10.40/3.92  
% 10.40/3.92  #Partial instantiations: 0
% 10.40/3.92  #Strategies tried      : 1
% 10.40/3.92  
% 10.40/3.92  Timing (in seconds)
% 10.40/3.92  ----------------------
% 10.40/3.92  Preprocessing        : 0.56
% 10.40/3.92  Parsing              : 0.29
% 10.40/3.92  CNF conversion       : 0.04
% 10.40/3.92  Main loop            : 2.38
% 10.40/3.92  Inferencing          : 0.77
% 10.40/3.92  Reduction            : 0.79
% 10.40/3.92  Demodulation         : 0.52
% 10.40/3.92  BG Simplification    : 0.10
% 10.40/3.92  Subsumption          : 0.50
% 10.40/3.92  Abstraction          : 0.10
% 10.40/3.92  MUC search           : 0.00
% 10.40/3.92  Cooper               : 0.00
% 10.40/3.92  Total                : 3.03
% 10.40/3.92  Index Insertion      : 0.00
% 10.40/3.93  Index Deletion       : 0.00
% 10.40/3.93  Index Matching       : 0.00
% 10.40/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
