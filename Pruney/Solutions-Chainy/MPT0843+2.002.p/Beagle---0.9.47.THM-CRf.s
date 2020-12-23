%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 19.63s
% Output     : CNFRefutation 19.93s
% Verified   : 
% Statistics : Number of formulae       :  154 (1221 expanded)
%              Number of leaves         :   27 ( 405 expanded)
%              Depth                    :   17
%              Number of atoms          :  371 (3421 expanded)
%              Number of equality atoms :   21 ( 329 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ! [D] :
                  ( r2_hidden(D,A)
                 => k11_relat_1(B,D) = k11_relat_1(C,D) )
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_113,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_123,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_14,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_73,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_87,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_271,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( m1_subset_1('#skF_1'(A_110,B_111,C_112,D_113),A_110)
      | r2_relset_1(A_110,B_111,C_112,D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_342,plain,(
    ! [C_115] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_3',C_115,'#skF_4'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',C_115,'#skF_4')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_271])).

tff(c_361,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_342])).

tff(c_364,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_40,plain,(
    ! [D_46,C_45,A_43,B_44] :
      ( D_46 = C_45
      | ~ r2_relset_1(A_43,B_44,C_45,D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_381,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_364,c_40])).

tff(c_384,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_381])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_394,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_42])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_394])).

tff(c_403,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_83,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_402,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_452,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( m1_subset_1('#skF_2'(A_121,B_122,C_123,D_124),B_122)
      | r2_relset_1(A_121,B_122,C_123,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_523,plain,(
    ! [C_126] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_3',C_126,'#skF_4'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',C_126,'#skF_4')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_452])).

tff(c_534,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_523])).

tff(c_544,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_534])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ r2_hidden(B_10,k11_relat_1(C_11,A_9))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_582,plain,(
    ! [D_127,C_132,B_129,A_130,F_128,E_131] :
      ( r2_hidden(k4_tarski(E_131,F_128),C_132)
      | ~ r2_hidden(k4_tarski(E_131,F_128),D_127)
      | ~ m1_subset_1(F_128,B_129)
      | ~ m1_subset_1(E_131,A_130)
      | ~ r2_relset_1(A_130,B_129,C_132,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1015,plain,(
    ! [B_204,A_206,B_203,C_202,C_205,A_201] :
      ( r2_hidden(k4_tarski(A_206,B_204),C_202)
      | ~ m1_subset_1(B_204,B_203)
      | ~ m1_subset_1(A_206,A_201)
      | ~ r2_relset_1(A_201,B_203,C_202,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_201,B_203)))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_201,B_203)))
      | ~ r2_hidden(B_204,k11_relat_1(C_205,A_206))
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_16,c_582])).

tff(c_1728,plain,(
    ! [A_325,C_326,A_327,C_328] :
      ( r2_hidden(k4_tarski(A_325,'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),C_326)
      | ~ m1_subset_1(A_325,A_327)
      | ~ r2_relset_1(A_327,'#skF_3',C_326,C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_327,'#skF_3')))
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,'#skF_3')))
      | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1(C_328,A_325))
      | ~ v1_relat_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_544,c_1015])).

tff(c_3610,plain,(
    ! [C_620,C_621] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),C_620)
      | ~ r2_relset_1('#skF_3','#skF_3',C_620,C_621)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1(C_621,'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
      | ~ v1_relat_1(C_621) ) ),
    inference(resolution,[status(thm)],[c_402,c_1728])).

tff(c_3612,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_3610])).

tff(c_3617,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48,c_3612])).

tff(c_3621,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3617])).

tff(c_8,plain,(
    ! [B_3,A_2] :
      ( m1_subset_1(B_3,A_2)
      | ~ v1_xboole_0(B_3)
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( r2_hidden(B_3,A_2)
      | ~ m1_subset_1(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [B_73,C_74,A_75] :
      ( r2_hidden(B_73,k11_relat_1(C_74,A_75))
      | ~ r2_hidden(k4_tarski(A_75,B_73),C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_129,plain,(
    ! [B_73,A_2,A_75] :
      ( r2_hidden(B_73,k11_relat_1(A_2,A_75))
      | ~ v1_relat_1(A_2)
      | ~ m1_subset_1(k4_tarski(A_75,B_73),A_2)
      | v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_736,plain,(
    ! [E_165,D_161,B_163,C_166,F_162,A_164] :
      ( r2_hidden(k4_tarski(E_165,F_162),D_161)
      | ~ r2_hidden(k4_tarski(E_165,F_162),C_166)
      | ~ m1_subset_1(F_162,B_163)
      | ~ m1_subset_1(E_165,A_164)
      | ~ r2_relset_1(A_164,B_163,C_166,D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163)))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_959,plain,(
    ! [A_190,B_191,B_189,A_193,D_194,C_192] :
      ( r2_hidden(k4_tarski(A_193,B_191),D_194)
      | ~ m1_subset_1(B_191,B_189)
      | ~ m1_subset_1(A_193,A_190)
      | ~ r2_relset_1(A_190,B_189,C_192,D_194)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ r2_hidden(B_191,k11_relat_1(C_192,A_193))
      | ~ v1_relat_1(C_192) ) ),
    inference(resolution,[status(thm)],[c_16,c_736])).

tff(c_1812,plain,(
    ! [A_337,D_338,A_339,C_340] :
      ( r2_hidden(k4_tarski(A_337,'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),D_338)
      | ~ m1_subset_1(A_337,A_339)
      | ~ r2_relset_1(A_339,'#skF_3',C_340,D_338)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_339,'#skF_3')))
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_339,'#skF_3')))
      | ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1(C_340,A_337))
      | ~ v1_relat_1(C_340) ) ),
    inference(resolution,[status(thm)],[c_402,c_959])).

tff(c_3486,plain,(
    ! [D_591,C_592] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),D_591)
      | ~ r2_relset_1('#skF_3','#skF_3',C_592,D_591)
      | ~ m1_subset_1(D_591,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1(C_592,'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
      | ~ v1_relat_1(C_592) ) ),
    inference(resolution,[status(thm)],[c_402,c_1812])).

tff(c_3488,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_3486])).

tff(c_3493,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48,c_3488])).

tff(c_3497,plain,(
    ~ r2_hidden('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3493])).

tff(c_3500,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_3497])).

tff(c_3506,plain,
    ( ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3500])).

tff(c_3508,plain,(
    ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3506])).

tff(c_3535,plain,
    ( ~ v1_xboole_0(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_3508])).

tff(c_3536,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3535])).

tff(c_3625,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_3621])).

tff(c_3631,plain,
    ( ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3625])).

tff(c_3632,plain,(
    ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3536,c_3631])).

tff(c_98,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_xboole_0(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_112,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_67,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [D_51] :
      ( k11_relat_1('#skF_5',D_51) = k11_relat_1('#skF_4',D_51)
      | ~ r2_hidden(D_51,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_72,plain,(
    ! [B_60] :
      ( k11_relat_1('#skF_5',B_60) = k11_relat_1('#skF_4',B_60)
      | ~ m1_subset_1(B_60,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_44])).

tff(c_130,plain,(
    ! [B_60] :
      ( k11_relat_1('#skF_5',B_60) = k11_relat_1('#skF_4',B_60)
      | ~ m1_subset_1(B_60,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_72])).

tff(c_410,plain,(
    k11_relat_1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')) = k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_402,c_130])).

tff(c_890,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_hidden(k4_tarski('#skF_1'(A_185,B_186,C_187,D_188),'#skF_2'(A_185,B_186,C_187,D_188)),C_187)
      | r2_hidden(k4_tarski('#skF_1'(A_185,B_186,C_187,D_188),'#skF_2'(A_185,B_186,C_187,D_188)),D_188)
      | r2_relset_1(A_185,B_186,C_187,D_188)
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [B_10,C_11,A_9] :
      ( r2_hidden(B_10,k11_relat_1(C_11,A_9))
      | ~ r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2067,plain,(
    ! [A_355,B_356,C_357,D_358] :
      ( r2_hidden('#skF_2'(A_355,B_356,C_357,D_358),k11_relat_1(C_357,'#skF_1'(A_355,B_356,C_357,D_358)))
      | ~ v1_relat_1(C_357)
      | r2_hidden(k4_tarski('#skF_1'(A_355,B_356,C_357,D_358),'#skF_2'(A_355,B_356,C_357,D_358)),D_358)
      | r2_relset_1(A_355,B_356,C_357,D_358)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356)))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(resolution,[status(thm)],[c_890,c_18])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( m1_subset_1(B_3,A_2)
      | ~ r2_hidden(B_3,A_2)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3726,plain,(
    ! [A_637,B_638,C_639,D_640] :
      ( m1_subset_1(k4_tarski('#skF_1'(A_637,B_638,C_639,D_640),'#skF_2'(A_637,B_638,C_639,D_640)),D_640)
      | v1_xboole_0(D_640)
      | r2_hidden('#skF_2'(A_637,B_638,C_639,D_640),k11_relat_1(C_639,'#skF_1'(A_637,B_638,C_639,D_640)))
      | ~ v1_relat_1(C_639)
      | r2_relset_1(A_637,B_638,C_639,D_640)
      | ~ m1_subset_1(D_640,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638)))
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638))) ) ),
    inference(resolution,[status(thm)],[c_2067,c_4])).

tff(c_3886,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_5')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_3726])).

tff(c_3955,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_87,c_3886])).

tff(c_3957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_3621,c_3536,c_3632,c_3955])).

tff(c_3959,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_3617])).

tff(c_3958,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3617])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18,D_32] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_16,B_17,C_18,D_32),'#skF_2'(A_16,B_17,C_18,D_32)),D_32)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_16,B_17,C_18,D_32),'#skF_2'(A_16,B_17,C_18,D_32)),C_18)
      | r2_relset_1(A_16,B_17,C_18,D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3961,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_5')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_3958,c_26])).

tff(c_3974,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_5')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_3961])).

tff(c_3975,plain,(
    ~ r2_hidden(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_3974])).

tff(c_4008,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_3975])).

tff(c_4027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_3959,c_410,c_4008])).

tff(c_4029,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3535])).

tff(c_286,plain,(
    ! [C_114] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_3',C_114,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',C_114,'#skF_5')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_271])).

tff(c_300,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_286])).

tff(c_309,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_300])).

tff(c_316,plain,(
    k11_relat_1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) = k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_309,c_130])).

tff(c_330,plain,(
    ! [B_73] :
      ( r2_hidden(B_73,k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),B_73),'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_129])).

tff(c_340,plain,(
    ! [B_73] :
      ( r2_hidden(B_73,k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),B_73),'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_330])).

tff(c_436,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_440,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_441,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_2])).

tff(c_4034,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4029,c_441])).

tff(c_4104,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4034,c_403])).

tff(c_4117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_4104])).

tff(c_4119,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_4527,plain,(
    ! [A_674,B_675,C_676,D_677] :
      ( r2_hidden(k4_tarski('#skF_1'(A_674,B_675,C_676,D_677),'#skF_2'(A_674,B_675,C_676,D_677)),C_676)
      | r2_hidden(k4_tarski('#skF_1'(A_674,B_675,C_676,D_677),'#skF_2'(A_674,B_675,C_676,D_677)),D_677)
      | r2_relset_1(A_674,B_675,C_676,D_677)
      | ~ m1_subset_1(D_677,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675)))
      | ~ m1_subset_1(C_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35202,plain,(
    ! [A_3061,B_3062,C_3063,D_3064] :
      ( r2_hidden('#skF_2'(A_3061,B_3062,C_3063,D_3064),k11_relat_1(C_3063,'#skF_1'(A_3061,B_3062,C_3063,D_3064)))
      | ~ v1_relat_1(C_3063)
      | r2_hidden(k4_tarski('#skF_1'(A_3061,B_3062,C_3063,D_3064),'#skF_2'(A_3061,B_3062,C_3063,D_3064)),D_3064)
      | r2_relset_1(A_3061,B_3062,C_3063,D_3064)
      | ~ m1_subset_1(D_3064,k1_zfmisc_1(k2_zfmisc_1(A_3061,B_3062)))
      | ~ m1_subset_1(C_3063,k1_zfmisc_1(k2_zfmisc_1(A_3061,B_3062))) ) ),
    inference(resolution,[status(thm)],[c_4527,c_18])).

tff(c_38632,plain,(
    ! [A_3457,B_3458,C_3459,D_3460] :
      ( r2_hidden('#skF_2'(A_3457,B_3458,C_3459,D_3460),k11_relat_1(D_3460,'#skF_1'(A_3457,B_3458,C_3459,D_3460)))
      | ~ v1_relat_1(D_3460)
      | r2_hidden('#skF_2'(A_3457,B_3458,C_3459,D_3460),k11_relat_1(C_3459,'#skF_1'(A_3457,B_3458,C_3459,D_3460)))
      | ~ v1_relat_1(C_3459)
      | r2_relset_1(A_3457,B_3458,C_3459,D_3460)
      | ~ m1_subset_1(D_3460,k1_zfmisc_1(k2_zfmisc_1(A_3457,B_3458)))
      | ~ m1_subset_1(C_3459,k1_zfmisc_1(k2_zfmisc_1(A_3457,B_3458))) ) ),
    inference(resolution,[status(thm)],[c_35202,c_18])).

tff(c_38675,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_4')
    | r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | ~ v1_relat_1('#skF_5')
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_38632])).

tff(c_38690,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
    | r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_87,c_90,c_38675])).

tff(c_38691,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4'),k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_38690])).

tff(c_137,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(k4_tarski(A_77,B_78),C_79)
      | ~ r2_hidden(B_78,k11_relat_1(C_79,A_77))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k4_tarski(A_77,B_78),C_79)
      | v1_xboole_0(C_79)
      | ~ r2_hidden(B_78,k11_relat_1(C_79,A_77))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_421,plain,(
    ! [B_78] :
      ( m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),B_78),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden(B_78,k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4')))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_149])).

tff(c_432,plain,(
    ! [B_78] :
      ( m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),B_78),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden(B_78,k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_421])).

tff(c_4136,plain,(
    ! [B_78] :
      ( m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),B_78),'#skF_5')
      | ~ r2_hidden(B_78,k11_relat_1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4119,c_432])).

tff(c_38704,plain,(
    m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38691,c_4136])).

tff(c_19566,plain,(
    ! [A_1853,B_1854,C_1855,D_1856] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1853,B_1854,C_1855,D_1856),'#skF_2'(A_1853,B_1854,C_1855,D_1856)),D_1856)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_1853,B_1854,C_1855,D_1856),'#skF_2'(A_1853,B_1854,C_1855,D_1856)),C_1855)
      | r2_relset_1(A_1853,B_1854,C_1855,D_1856)
      | ~ m1_subset_1(D_1856,k1_zfmisc_1(k2_zfmisc_1(A_1853,B_1854)))
      | ~ m1_subset_1(C_1855,k1_zfmisc_1(k2_zfmisc_1(A_1853,B_1854))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36944,plain,(
    ! [A_3211,B_3212,C_3213,C_3214] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3211,B_3212,C_3213,C_3214),'#skF_2'(A_3211,B_3212,C_3213,C_3214)),C_3213)
      | r2_relset_1(A_3211,B_3212,C_3213,C_3214)
      | ~ m1_subset_1(C_3214,k1_zfmisc_1(k2_zfmisc_1(A_3211,B_3212)))
      | ~ m1_subset_1(C_3213,k1_zfmisc_1(k2_zfmisc_1(A_3211,B_3212)))
      | ~ r2_hidden('#skF_2'(A_3211,B_3212,C_3213,C_3214),k11_relat_1(C_3214,'#skF_1'(A_3211,B_3212,C_3213,C_3214)))
      | ~ v1_relat_1(C_3214) ) ),
    inference(resolution,[status(thm)],[c_16,c_19566])).

tff(c_39452,plain,(
    ! [A_3487,B_3488,A_3489,C_3490] :
      ( r2_relset_1(A_3487,B_3488,A_3489,C_3490)
      | ~ m1_subset_1(C_3490,k1_zfmisc_1(k2_zfmisc_1(A_3487,B_3488)))
      | ~ m1_subset_1(A_3489,k1_zfmisc_1(k2_zfmisc_1(A_3487,B_3488)))
      | ~ r2_hidden('#skF_2'(A_3487,B_3488,A_3489,C_3490),k11_relat_1(C_3490,'#skF_1'(A_3487,B_3488,A_3489,C_3490)))
      | ~ v1_relat_1(C_3490)
      | ~ m1_subset_1(k4_tarski('#skF_1'(A_3487,B_3488,A_3489,C_3490),'#skF_2'(A_3487,B_3488,A_3489,C_3490)),A_3489)
      | v1_xboole_0(A_3489) ) ),
    inference(resolution,[status(thm)],[c_6,c_36944])).

tff(c_39456,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_relat_1('#skF_4')
    | ~ m1_subset_1(k4_tarski('#skF_1'('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_3','#skF_5','#skF_4')),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38691,c_39452])).

tff(c_39489,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38704,c_90,c_46,c_48,c_39456])).

tff(c_39491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4119,c_403,c_39489])).

tff(c_39493,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_111,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_39508,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39493,c_111])).

tff(c_39501,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_39493,c_2])).

tff(c_39492,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_39497,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_39492,c_2])).

tff(c_39509,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39501,c_39497])).

tff(c_39502,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39497,c_2])).

tff(c_39525,plain,(
    ! [A_3491] :
      ( A_3491 = '#skF_3'
      | ~ v1_xboole_0(A_3491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39509,c_39502])).

tff(c_39532,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39508,c_39525])).

tff(c_39518,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39509,c_42])).

tff(c_39567,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39532,c_39532,c_39532,c_39518])).

tff(c_39517,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39509,c_46])).

tff(c_39568,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39532,c_39532,c_39532,c_39517])).

tff(c_38,plain,(
    ! [A_43,B_44,D_46] :
      ( r2_relset_1(A_43,B_44,D_46,D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_39570,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_39568,c_38])).

tff(c_39583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39567,c_39570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.63/11.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.63/11.11  
% 19.63/11.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.63/11.11  %$ r2_relset_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 19.63/11.11  
% 19.63/11.11  %Foreground sorts:
% 19.63/11.11  
% 19.63/11.11  
% 19.63/11.11  %Background operators:
% 19.63/11.11  
% 19.63/11.11  
% 19.63/11.11  %Foreground operators:
% 19.63/11.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.63/11.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 19.63/11.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.63/11.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 19.63/11.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.63/11.11  tff('#skF_5', type, '#skF_5': $i).
% 19.63/11.11  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 19.63/11.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 19.63/11.11  tff('#skF_3', type, '#skF_3': $i).
% 19.63/11.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.63/11.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.63/11.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.63/11.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.63/11.11  tff('#skF_4', type, '#skF_4': $i).
% 19.63/11.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.63/11.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 19.63/11.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.63/11.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.63/11.11  
% 19.93/11.14  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 19.93/11.14  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 19.93/11.14  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 19.93/11.14  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 19.93/11.14  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relset_1)).
% 19.93/11.14  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 19.93/11.14  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 19.93/11.14  tff(f_64, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 19.93/11.14  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 19.93/11.14  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.93/11.14  tff(c_113, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.93/11.14  tff(c_123, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_113])).
% 19.93/11.14  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.93/11.14  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.93/11.14  tff(c_73, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.93/11.14  tff(c_80, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_73])).
% 19.93/11.14  tff(c_87, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 19.93/11.14  tff(c_271, plain, (![A_110, B_111, C_112, D_113]: (m1_subset_1('#skF_1'(A_110, B_111, C_112, D_113), A_110) | r2_relset_1(A_110, B_111, C_112, D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_342, plain, (![C_115]: (m1_subset_1('#skF_1'('#skF_3', '#skF_3', C_115, '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', C_115, '#skF_4') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_48, c_271])).
% 19.93/11.14  tff(c_361, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_342])).
% 19.93/11.14  tff(c_364, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_361])).
% 19.93/11.14  tff(c_40, plain, (![D_46, C_45, A_43, B_44]: (D_46=C_45 | ~r2_relset_1(A_43, B_44, C_45, D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.93/11.14  tff(c_381, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_364, c_40])).
% 19.93/11.14  tff(c_384, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_381])).
% 19.93/11.14  tff(c_42, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.93/11.14  tff(c_394, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_42])).
% 19.93/11.14  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_394])).
% 19.93/11.14  tff(c_403, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_361])).
% 19.93/11.14  tff(c_83, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 19.93/11.14  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83])).
% 19.93/11.14  tff(c_402, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_361])).
% 19.93/11.14  tff(c_452, plain, (![A_121, B_122, C_123, D_124]: (m1_subset_1('#skF_2'(A_121, B_122, C_123, D_124), B_122) | r2_relset_1(A_121, B_122, C_123, D_124) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_523, plain, (![C_126]: (m1_subset_1('#skF_2'('#skF_3', '#skF_3', C_126, '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', C_126, '#skF_4') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_48, c_452])).
% 19.93/11.14  tff(c_534, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_523])).
% 19.93/11.14  tff(c_544, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_403, c_534])).
% 19.93/11.14  tff(c_16, plain, (![A_9, B_10, C_11]: (r2_hidden(k4_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, k11_relat_1(C_11, A_9)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.93/11.14  tff(c_582, plain, (![D_127, C_132, B_129, A_130, F_128, E_131]: (r2_hidden(k4_tarski(E_131, F_128), C_132) | ~r2_hidden(k4_tarski(E_131, F_128), D_127) | ~m1_subset_1(F_128, B_129) | ~m1_subset_1(E_131, A_130) | ~r2_relset_1(A_130, B_129, C_132, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_1015, plain, (![B_204, A_206, B_203, C_202, C_205, A_201]: (r2_hidden(k4_tarski(A_206, B_204), C_202) | ~m1_subset_1(B_204, B_203) | ~m1_subset_1(A_206, A_201) | ~r2_relset_1(A_201, B_203, C_202, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_201, B_203))) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_201, B_203))) | ~r2_hidden(B_204, k11_relat_1(C_205, A_206)) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_16, c_582])).
% 19.93/11.14  tff(c_1728, plain, (![A_325, C_326, A_327, C_328]: (r2_hidden(k4_tarski(A_325, '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), C_326) | ~m1_subset_1(A_325, A_327) | ~r2_relset_1(A_327, '#skF_3', C_326, C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_327, '#skF_3'))) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1(C_328, A_325)) | ~v1_relat_1(C_328))), inference(resolution, [status(thm)], [c_544, c_1015])).
% 19.93/11.14  tff(c_3610, plain, (![C_620, C_621]: (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), C_620) | ~r2_relset_1('#skF_3', '#skF_3', C_620, C_621) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1(C_621, '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1(C_621))), inference(resolution, [status(thm)], [c_402, c_1728])).
% 19.93/11.14  tff(c_3612, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_123, c_3610])).
% 19.93/11.14  tff(c_3617, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48, c_3612])).
% 19.93/11.14  tff(c_3621, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_3617])).
% 19.93/11.14  tff(c_8, plain, (![B_3, A_2]: (m1_subset_1(B_3, A_2) | ~v1_xboole_0(B_3) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.93/11.14  tff(c_6, plain, (![B_3, A_2]: (r2_hidden(B_3, A_2) | ~m1_subset_1(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.93/11.14  tff(c_124, plain, (![B_73, C_74, A_75]: (r2_hidden(B_73, k11_relat_1(C_74, A_75)) | ~r2_hidden(k4_tarski(A_75, B_73), C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.93/11.14  tff(c_129, plain, (![B_73, A_2, A_75]: (r2_hidden(B_73, k11_relat_1(A_2, A_75)) | ~v1_relat_1(A_2) | ~m1_subset_1(k4_tarski(A_75, B_73), A_2) | v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_6, c_124])).
% 19.93/11.14  tff(c_736, plain, (![E_165, D_161, B_163, C_166, F_162, A_164]: (r2_hidden(k4_tarski(E_165, F_162), D_161) | ~r2_hidden(k4_tarski(E_165, F_162), C_166) | ~m1_subset_1(F_162, B_163) | ~m1_subset_1(E_165, A_164) | ~r2_relset_1(A_164, B_163, C_166, D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_959, plain, (![A_190, B_191, B_189, A_193, D_194, C_192]: (r2_hidden(k4_tarski(A_193, B_191), D_194) | ~m1_subset_1(B_191, B_189) | ~m1_subset_1(A_193, A_190) | ~r2_relset_1(A_190, B_189, C_192, D_194) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~r2_hidden(B_191, k11_relat_1(C_192, A_193)) | ~v1_relat_1(C_192))), inference(resolution, [status(thm)], [c_16, c_736])).
% 19.93/11.14  tff(c_1812, plain, (![A_337, D_338, A_339, C_340]: (r2_hidden(k4_tarski(A_337, '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), D_338) | ~m1_subset_1(A_337, A_339) | ~r2_relset_1(A_339, '#skF_3', C_340, D_338) | ~m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_339, '#skF_3'))) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_339, '#skF_3'))) | ~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1(C_340, A_337)) | ~v1_relat_1(C_340))), inference(resolution, [status(thm)], [c_402, c_959])).
% 19.93/11.14  tff(c_3486, plain, (![D_591, C_592]: (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), D_591) | ~r2_relset_1('#skF_3', '#skF_3', C_592, D_591) | ~m1_subset_1(D_591, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1(C_592, '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1(C_592))), inference(resolution, [status(thm)], [c_402, c_1812])).
% 19.93/11.14  tff(c_3488, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_123, c_3486])).
% 19.93/11.14  tff(c_3493, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48, c_3488])).
% 19.93/11.14  tff(c_3497, plain, (~r2_hidden('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_3493])).
% 19.93/11.14  tff(c_3500, plain, (~v1_relat_1('#skF_4') | ~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_129, c_3497])).
% 19.93/11.14  tff(c_3506, plain, (~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3500])).
% 19.93/11.14  tff(c_3508, plain, (~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_3506])).
% 19.93/11.14  tff(c_3535, plain, (~v1_xboole_0(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8, c_3508])).
% 19.93/11.14  tff(c_3536, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3535])).
% 19.93/11.14  tff(c_3625, plain, (~v1_relat_1('#skF_4') | ~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_129, c_3621])).
% 19.93/11.14  tff(c_3631, plain, (~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3625])).
% 19.93/11.14  tff(c_3632, plain, (~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3536, c_3631])).
% 19.93/11.14  tff(c_98, plain, (![C_67, A_68, B_69]: (v1_xboole_0(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.93/11.14  tff(c_110, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_98])).
% 19.93/11.14  tff(c_112, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 19.93/11.14  tff(c_67, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.93/11.14  tff(c_44, plain, (![D_51]: (k11_relat_1('#skF_5', D_51)=k11_relat_1('#skF_4', D_51) | ~r2_hidden(D_51, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.93/11.14  tff(c_72, plain, (![B_60]: (k11_relat_1('#skF_5', B_60)=k11_relat_1('#skF_4', B_60) | ~m1_subset_1(B_60, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_67, c_44])).
% 19.93/11.14  tff(c_130, plain, (![B_60]: (k11_relat_1('#skF_5', B_60)=k11_relat_1('#skF_4', B_60) | ~m1_subset_1(B_60, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_112, c_72])).
% 19.93/11.14  tff(c_410, plain, (k11_relat_1('#skF_5', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))=k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_402, c_130])).
% 19.93/11.14  tff(c_890, plain, (![A_185, B_186, C_187, D_188]: (r2_hidden(k4_tarski('#skF_1'(A_185, B_186, C_187, D_188), '#skF_2'(A_185, B_186, C_187, D_188)), C_187) | r2_hidden(k4_tarski('#skF_1'(A_185, B_186, C_187, D_188), '#skF_2'(A_185, B_186, C_187, D_188)), D_188) | r2_relset_1(A_185, B_186, C_187, D_188) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_18, plain, (![B_10, C_11, A_9]: (r2_hidden(B_10, k11_relat_1(C_11, A_9)) | ~r2_hidden(k4_tarski(A_9, B_10), C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.93/11.14  tff(c_2067, plain, (![A_355, B_356, C_357, D_358]: (r2_hidden('#skF_2'(A_355, B_356, C_357, D_358), k11_relat_1(C_357, '#skF_1'(A_355, B_356, C_357, D_358))) | ~v1_relat_1(C_357) | r2_hidden(k4_tarski('#skF_1'(A_355, B_356, C_357, D_358), '#skF_2'(A_355, B_356, C_357, D_358)), D_358) | r2_relset_1(A_355, B_356, C_357, D_358) | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(resolution, [status(thm)], [c_890, c_18])).
% 19.93/11.14  tff(c_4, plain, (![B_3, A_2]: (m1_subset_1(B_3, A_2) | ~r2_hidden(B_3, A_2) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.93/11.14  tff(c_3726, plain, (![A_637, B_638, C_639, D_640]: (m1_subset_1(k4_tarski('#skF_1'(A_637, B_638, C_639, D_640), '#skF_2'(A_637, B_638, C_639, D_640)), D_640) | v1_xboole_0(D_640) | r2_hidden('#skF_2'(A_637, B_638, C_639, D_640), k11_relat_1(C_639, '#skF_1'(A_637, B_638, C_639, D_640))) | ~v1_relat_1(C_639) | r2_relset_1(A_637, B_638, C_639, D_640) | ~m1_subset_1(D_640, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))) | ~m1_subset_1(C_639, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))))), inference(resolution, [status(thm)], [c_2067, c_4])).
% 19.93/11.14  tff(c_3886, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4') | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_5') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_410, c_3726])).
% 19.93/11.14  tff(c_3955, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4') | v1_xboole_0('#skF_4') | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_87, c_3886])).
% 19.93/11.14  tff(c_3957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_3621, c_3536, c_3632, c_3955])).
% 19.93/11.14  tff(c_3959, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_3617])).
% 19.93/11.14  tff(c_3958, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_3617])).
% 19.93/11.14  tff(c_26, plain, (![A_16, B_17, C_18, D_32]: (~r2_hidden(k4_tarski('#skF_1'(A_16, B_17, C_18, D_32), '#skF_2'(A_16, B_17, C_18, D_32)), D_32) | ~r2_hidden(k4_tarski('#skF_1'(A_16, B_17, C_18, D_32), '#skF_2'(A_16, B_17, C_18, D_32)), C_18) | r2_relset_1(A_16, B_17, C_18, D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_3961, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_5') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_3958, c_26])).
% 19.93/11.14  tff(c_3974, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_5') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_3961])).
% 19.93/11.14  tff(c_3975, plain, (~r2_hidden(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_403, c_3974])).
% 19.93/11.14  tff(c_4008, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_5', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_3975])).
% 19.93/11.14  tff(c_4027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_3959, c_410, c_4008])).
% 19.93/11.14  tff(c_4029, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3535])).
% 19.93/11.14  tff(c_286, plain, (![C_114]: (m1_subset_1('#skF_1'('#skF_3', '#skF_3', C_114, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', C_114, '#skF_5') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_271])).
% 19.93/11.14  tff(c_300, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_286])).
% 19.93/11.14  tff(c_309, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_300])).
% 19.93/11.14  tff(c_316, plain, (k11_relat_1('#skF_5', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))=k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_309, c_130])).
% 19.93/11.14  tff(c_330, plain, (![B_73]: (r2_hidden(B_73, k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), B_73), '#skF_5') | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_129])).
% 19.93/11.14  tff(c_340, plain, (![B_73]: (r2_hidden(B_73, k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_4', '#skF_5'), B_73), '#skF_5') | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_330])).
% 19.93/11.14  tff(c_436, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_340])).
% 19.93/11.14  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.93/11.14  tff(c_440, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_436, c_2])).
% 19.93/11.14  tff(c_441, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_2])).
% 19.93/11.14  tff(c_4034, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4029, c_441])).
% 19.93/11.14  tff(c_4104, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4034, c_403])).
% 19.93/11.14  tff(c_4117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_4104])).
% 19.93/11.14  tff(c_4119, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_340])).
% 19.93/11.14  tff(c_4527, plain, (![A_674, B_675, C_676, D_677]: (r2_hidden(k4_tarski('#skF_1'(A_674, B_675, C_676, D_677), '#skF_2'(A_674, B_675, C_676, D_677)), C_676) | r2_hidden(k4_tarski('#skF_1'(A_674, B_675, C_676, D_677), '#skF_2'(A_674, B_675, C_676, D_677)), D_677) | r2_relset_1(A_674, B_675, C_676, D_677) | ~m1_subset_1(D_677, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))) | ~m1_subset_1(C_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_35202, plain, (![A_3061, B_3062, C_3063, D_3064]: (r2_hidden('#skF_2'(A_3061, B_3062, C_3063, D_3064), k11_relat_1(C_3063, '#skF_1'(A_3061, B_3062, C_3063, D_3064))) | ~v1_relat_1(C_3063) | r2_hidden(k4_tarski('#skF_1'(A_3061, B_3062, C_3063, D_3064), '#skF_2'(A_3061, B_3062, C_3063, D_3064)), D_3064) | r2_relset_1(A_3061, B_3062, C_3063, D_3064) | ~m1_subset_1(D_3064, k1_zfmisc_1(k2_zfmisc_1(A_3061, B_3062))) | ~m1_subset_1(C_3063, k1_zfmisc_1(k2_zfmisc_1(A_3061, B_3062))))), inference(resolution, [status(thm)], [c_4527, c_18])).
% 19.93/11.14  tff(c_38632, plain, (![A_3457, B_3458, C_3459, D_3460]: (r2_hidden('#skF_2'(A_3457, B_3458, C_3459, D_3460), k11_relat_1(D_3460, '#skF_1'(A_3457, B_3458, C_3459, D_3460))) | ~v1_relat_1(D_3460) | r2_hidden('#skF_2'(A_3457, B_3458, C_3459, D_3460), k11_relat_1(C_3459, '#skF_1'(A_3457, B_3458, C_3459, D_3460))) | ~v1_relat_1(C_3459) | r2_relset_1(A_3457, B_3458, C_3459, D_3460) | ~m1_subset_1(D_3460, k1_zfmisc_1(k2_zfmisc_1(A_3457, B_3458))) | ~m1_subset_1(C_3459, k1_zfmisc_1(k2_zfmisc_1(A_3457, B_3458))))), inference(resolution, [status(thm)], [c_35202, c_18])).
% 19.93/11.14  tff(c_38675, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_4') | r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_5') | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_410, c_38632])).
% 19.93/11.14  tff(c_38690, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_87, c_90, c_38675])).
% 19.93/11.14  tff(c_38691, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_403, c_38690])).
% 19.93/11.14  tff(c_137, plain, (![A_77, B_78, C_79]: (r2_hidden(k4_tarski(A_77, B_78), C_79) | ~r2_hidden(B_78, k11_relat_1(C_79, A_77)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.93/11.14  tff(c_149, plain, (![A_77, B_78, C_79]: (m1_subset_1(k4_tarski(A_77, B_78), C_79) | v1_xboole_0(C_79) | ~r2_hidden(B_78, k11_relat_1(C_79, A_77)) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_137, c_4])).
% 19.93/11.14  tff(c_421, plain, (![B_78]: (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), B_78), '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden(B_78, k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_149])).
% 19.93/11.14  tff(c_432, plain, (![B_78]: (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), B_78), '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden(B_78, k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_421])).
% 19.93/11.14  tff(c_4136, plain, (![B_78]: (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), B_78), '#skF_5') | ~r2_hidden(B_78, k11_relat_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_4119, c_432])).
% 19.93/11.14  tff(c_38704, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_5')), inference(resolution, [status(thm)], [c_38691, c_4136])).
% 19.93/11.14  tff(c_19566, plain, (![A_1853, B_1854, C_1855, D_1856]: (~r2_hidden(k4_tarski('#skF_1'(A_1853, B_1854, C_1855, D_1856), '#skF_2'(A_1853, B_1854, C_1855, D_1856)), D_1856) | ~r2_hidden(k4_tarski('#skF_1'(A_1853, B_1854, C_1855, D_1856), '#skF_2'(A_1853, B_1854, C_1855, D_1856)), C_1855) | r2_relset_1(A_1853, B_1854, C_1855, D_1856) | ~m1_subset_1(D_1856, k1_zfmisc_1(k2_zfmisc_1(A_1853, B_1854))) | ~m1_subset_1(C_1855, k1_zfmisc_1(k2_zfmisc_1(A_1853, B_1854))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.93/11.14  tff(c_36944, plain, (![A_3211, B_3212, C_3213, C_3214]: (~r2_hidden(k4_tarski('#skF_1'(A_3211, B_3212, C_3213, C_3214), '#skF_2'(A_3211, B_3212, C_3213, C_3214)), C_3213) | r2_relset_1(A_3211, B_3212, C_3213, C_3214) | ~m1_subset_1(C_3214, k1_zfmisc_1(k2_zfmisc_1(A_3211, B_3212))) | ~m1_subset_1(C_3213, k1_zfmisc_1(k2_zfmisc_1(A_3211, B_3212))) | ~r2_hidden('#skF_2'(A_3211, B_3212, C_3213, C_3214), k11_relat_1(C_3214, '#skF_1'(A_3211, B_3212, C_3213, C_3214))) | ~v1_relat_1(C_3214))), inference(resolution, [status(thm)], [c_16, c_19566])).
% 19.93/11.14  tff(c_39452, plain, (![A_3487, B_3488, A_3489, C_3490]: (r2_relset_1(A_3487, B_3488, A_3489, C_3490) | ~m1_subset_1(C_3490, k1_zfmisc_1(k2_zfmisc_1(A_3487, B_3488))) | ~m1_subset_1(A_3489, k1_zfmisc_1(k2_zfmisc_1(A_3487, B_3488))) | ~r2_hidden('#skF_2'(A_3487, B_3488, A_3489, C_3490), k11_relat_1(C_3490, '#skF_1'(A_3487, B_3488, A_3489, C_3490))) | ~v1_relat_1(C_3490) | ~m1_subset_1(k4_tarski('#skF_1'(A_3487, B_3488, A_3489, C_3490), '#skF_2'(A_3487, B_3488, A_3489, C_3490)), A_3489) | v1_xboole_0(A_3489))), inference(resolution, [status(thm)], [c_6, c_36944])).
% 19.93/11.14  tff(c_39456, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_relat_1('#skF_4') | ~m1_subset_1(k4_tarski('#skF_1'('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_2'('#skF_3', '#skF_3', '#skF_5', '#skF_4')), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38691, c_39452])).
% 19.93/11.14  tff(c_39489, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38704, c_90, c_46, c_48, c_39456])).
% 19.93/11.14  tff(c_39491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4119, c_403, c_39489])).
% 19.93/11.14  tff(c_39493, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_110])).
% 19.93/11.14  tff(c_111, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_98])).
% 19.93/11.14  tff(c_39508, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39493, c_111])).
% 19.93/11.14  tff(c_39501, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_39493, c_2])).
% 19.93/11.14  tff(c_39492, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_110])).
% 19.93/11.14  tff(c_39497, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_39492, c_2])).
% 19.93/11.14  tff(c_39509, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_39501, c_39497])).
% 19.93/11.14  tff(c_39502, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_39497, c_2])).
% 19.93/11.14  tff(c_39525, plain, (![A_3491]: (A_3491='#skF_3' | ~v1_xboole_0(A_3491))), inference(demodulation, [status(thm), theory('equality')], [c_39509, c_39502])).
% 19.93/11.14  tff(c_39532, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_39508, c_39525])).
% 19.93/11.14  tff(c_39518, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39509, c_42])).
% 19.93/11.14  tff(c_39567, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39532, c_39532, c_39532, c_39518])).
% 19.93/11.14  tff(c_39517, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_39509, c_46])).
% 19.93/11.14  tff(c_39568, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_39532, c_39532, c_39532, c_39517])).
% 19.93/11.14  tff(c_38, plain, (![A_43, B_44, D_46]: (r2_relset_1(A_43, B_44, D_46, D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.93/11.14  tff(c_39570, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_39568, c_38])).
% 19.93/11.14  tff(c_39583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39567, c_39570])).
% 19.93/11.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.93/11.14  
% 19.93/11.14  Inference rules
% 19.93/11.14  ----------------------
% 19.93/11.14  #Ref     : 0
% 19.93/11.14  #Sup     : 10073
% 19.93/11.14  #Fact    : 12
% 19.93/11.14  #Define  : 0
% 19.93/11.14  #Split   : 105
% 19.93/11.14  #Chain   : 0
% 19.93/11.14  #Close   : 0
% 19.93/11.14  
% 19.93/11.14  Ordering : KBO
% 19.93/11.14  
% 19.93/11.14  Simplification rules
% 19.93/11.14  ----------------------
% 19.93/11.14  #Subsume      : 1396
% 19.93/11.14  #Demod        : 3757
% 19.93/11.14  #Tautology    : 878
% 19.93/11.14  #SimpNegUnit  : 812
% 19.93/11.14  #BackRed      : 138
% 19.93/11.14  
% 19.93/11.14  #Partial instantiations: 0
% 19.93/11.14  #Strategies tried      : 1
% 19.93/11.14  
% 19.93/11.14  Timing (in seconds)
% 19.93/11.14  ----------------------
% 19.93/11.15  Preprocessing        : 0.32
% 19.93/11.15  Parsing              : 0.16
% 19.93/11.15  CNF conversion       : 0.02
% 19.93/11.15  Main loop            : 10.03
% 19.93/11.15  Inferencing          : 1.57
% 19.93/11.15  Reduction            : 2.36
% 19.93/11.15  Demodulation         : 1.65
% 19.93/11.15  BG Simplification    : 0.26
% 19.93/11.15  Subsumption          : 5.27
% 19.93/11.15  Abstraction          : 0.35
% 19.93/11.15  MUC search           : 0.00
% 19.93/11.15  Cooper               : 0.00
% 19.93/11.15  Total                : 10.41
% 19.93/11.15  Index Insertion      : 0.00
% 19.93/11.15  Index Deletion       : 0.00
% 19.93/11.15  Index Matching       : 0.00
% 19.93/11.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
