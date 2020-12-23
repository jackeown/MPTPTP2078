%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 226 expanded)
%              Number of leaves         :   47 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 480 expanded)
%              Number of equality atoms :  112 ( 232 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_155,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_173,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_181,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_173])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_181,c_38])).

tff(c_202,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_343,plain,(
    ! [B_148,A_149] :
      ( k1_tarski(k1_funct_1(B_148,A_149)) = k2_relat_1(B_148)
      | k1_tarski(A_149) != k1_relat_1(B_148)
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_314,plain,(
    ! [A_141,B_142,C_143] :
      ( k2_relset_1(A_141,B_142,C_143) = k2_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_322,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_314])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_331,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_76])).

tff(c_349,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_331])).

tff(c_377,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84,c_349])).

tff(c_212,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_220,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_212])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_689,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( k1_enumset1(A_225,B_226,C_227) = D_228
      | k2_tarski(A_225,C_227) = D_228
      | k2_tarski(B_226,C_227) = D_228
      | k2_tarski(A_225,B_226) = D_228
      | k1_tarski(C_227) = D_228
      | k1_tarski(B_226) = D_228
      | k1_tarski(A_225) = D_228
      | k1_xboole_0 = D_228
      | ~ r1_tarski(D_228,k1_enumset1(A_225,B_226,C_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_717,plain,(
    ! [A_3,B_4,D_228] :
      ( k1_enumset1(A_3,A_3,B_4) = D_228
      | k2_tarski(A_3,B_4) = D_228
      | k2_tarski(A_3,B_4) = D_228
      | k2_tarski(A_3,A_3) = D_228
      | k1_tarski(B_4) = D_228
      | k1_tarski(A_3) = D_228
      | k1_tarski(A_3) = D_228
      | k1_xboole_0 = D_228
      | ~ r1_tarski(D_228,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_689])).

tff(c_851,plain,(
    ! [A_282,B_283,D_284] :
      ( k2_tarski(A_282,B_283) = D_284
      | k2_tarski(A_282,B_283) = D_284
      | k2_tarski(A_282,B_283) = D_284
      | k1_tarski(A_282) = D_284
      | k1_tarski(B_283) = D_284
      | k1_tarski(A_282) = D_284
      | k1_tarski(A_282) = D_284
      | k1_xboole_0 = D_284
      | ~ r1_tarski(D_284,k2_tarski(A_282,B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_717])).

tff(c_890,plain,(
    ! [A_285,B_286,B_287] :
      ( k2_tarski(A_285,B_286) = k1_relat_1(B_287)
      | k1_tarski(B_286) = k1_relat_1(B_287)
      | k1_tarski(A_285) = k1_relat_1(B_287)
      | k1_relat_1(B_287) = k1_xboole_0
      | ~ v4_relat_1(B_287,k2_tarski(A_285,B_286))
      | ~ v1_relat_1(B_287) ) ),
    inference(resolution,[status(thm)],[c_34,c_851])).

tff(c_897,plain,(
    ! [A_2,B_287] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_287)
      | k1_tarski(A_2) = k1_relat_1(B_287)
      | k1_tarski(A_2) = k1_relat_1(B_287)
      | k1_relat_1(B_287) = k1_xboole_0
      | ~ v4_relat_1(B_287,k1_tarski(A_2))
      | ~ v1_relat_1(B_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_890])).

tff(c_914,plain,(
    ! [A_292,B_293] :
      ( k1_tarski(A_292) = k1_relat_1(B_293)
      | k1_tarski(A_292) = k1_relat_1(B_293)
      | k1_tarski(A_292) = k1_relat_1(B_293)
      | k1_relat_1(B_293) = k1_xboole_0
      | ~ v4_relat_1(B_293,k1_tarski(A_292))
      | ~ v1_relat_1(B_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_897])).

tff(c_920,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_220,c_914])).

tff(c_927,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_920])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_377,c_927])).

tff(c_930,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_931,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_946,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_931])).

tff(c_1106,plain,(
    ! [B_349,A_350] :
      ( k1_tarski(k1_funct_1(B_349,A_350)) = k2_relat_1(B_349)
      | k1_tarski(A_350) != k1_relat_1(B_349)
      | ~ v1_funct_1(B_349)
      | ~ v1_relat_1(B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_938,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_28])).

tff(c_1084,plain,(
    ! [A_342,B_343,C_344] :
      ( k2_relset_1(A_342,B_343,C_344) = k2_relat_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1089,plain,(
    ! [A_342,B_343] : k2_relset_1(A_342,B_343,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_938,c_1084])).

tff(c_1090,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_76])).

tff(c_1112,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_1090])).

tff(c_1140,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84,c_946,c_1112])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_940,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_74,plain,(
    ! [B_60,A_59,C_61] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_59,B_60,C_61) = A_59
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1291,plain,(
    ! [B_377,A_378,C_379] :
      ( B_377 = '#skF_6'
      | k1_relset_1(A_378,B_377,C_379) = A_378
      | ~ v1_funct_2(C_379,A_378,B_377)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_378,B_377))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_74])).

tff(c_1298,plain,(
    ! [B_381,A_382] :
      ( B_381 = '#skF_6'
      | k1_relset_1(A_382,B_381,'#skF_6') = A_382
      | ~ v1_funct_2('#skF_6',A_382,B_381) ) ),
    inference(resolution,[status(thm)],[c_938,c_1291])).

tff(c_1310,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1298])).

tff(c_1318,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1310])).

tff(c_58,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_936,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | A_45 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_939,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_2])).

tff(c_1337,plain,(
    ! [D_393,A_394,B_395,C_396] :
      ( r2_hidden(k4_tarski(D_393,'#skF_2'(A_394,B_395,C_396,D_393)),C_396)
      | ~ r2_hidden(D_393,B_395)
      | k1_relset_1(B_395,A_394,C_396) != B_395
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(B_395,A_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1455,plain,(
    ! [C_423,D_424,A_425,B_426] :
      ( ~ r1_tarski(C_423,k4_tarski(D_424,'#skF_2'(A_425,B_426,C_423,D_424)))
      | ~ r2_hidden(D_424,B_426)
      | k1_relset_1(B_426,A_425,C_423) != B_426
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(B_426,A_425))) ) ),
    inference(resolution,[status(thm)],[c_1337,c_42])).

tff(c_1463,plain,(
    ! [D_424,B_426,A_425] :
      ( ~ r2_hidden(D_424,B_426)
      | k1_relset_1(B_426,A_425,'#skF_6') != B_426
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_426,A_425))) ) ),
    inference(resolution,[status(thm)],[c_939,c_1455])).

tff(c_1468,plain,(
    ! [D_427,B_428,A_429] :
      ( ~ r2_hidden(D_427,B_428)
      | k1_relset_1(B_428,A_429,'#skF_6') != B_428 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1463])).

tff(c_1478,plain,(
    ! [A_430,A_431] :
      ( k1_relset_1(A_430,A_431,'#skF_6') != A_430
      | A_430 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_936,c_1468])).

tff(c_1481,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1318,c_1478])).

tff(c_1488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.71  
% 3.85/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 3.85/1.71  
% 3.85/1.71  %Foreground sorts:
% 3.85/1.71  
% 3.85/1.71  
% 3.85/1.71  %Background operators:
% 3.85/1.71  
% 3.85/1.71  
% 3.85/1.71  %Foreground operators:
% 3.85/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.85/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.85/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.71  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.85/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.85/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.85/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.71  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.85/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.71  
% 3.85/1.73  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.85/1.73  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.85/1.73  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.85/1.73  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.85/1.73  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.85/1.73  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.73  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.73  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.85/1.73  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.73  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.85/1.73  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.85/1.73  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.85/1.73  tff(f_137, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.85/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.73  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.85/1.73  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.85/1.73  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.85/1.73  tff(c_173, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.73  tff(c_181, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_173])).
% 3.85/1.73  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.85/1.73  tff(c_38, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.85/1.73  tff(c_190, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_181, c_38])).
% 3.85/1.73  tff(c_202, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_190])).
% 3.85/1.73  tff(c_343, plain, (![B_148, A_149]: (k1_tarski(k1_funct_1(B_148, A_149))=k2_relat_1(B_148) | k1_tarski(A_149)!=k1_relat_1(B_148) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.73  tff(c_314, plain, (![A_141, B_142, C_143]: (k2_relset_1(A_141, B_142, C_143)=k2_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.85/1.73  tff(c_322, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_314])).
% 3.85/1.73  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.85/1.73  tff(c_331, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_76])).
% 3.85/1.73  tff(c_349, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_343, c_331])).
% 3.85/1.73  tff(c_377, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_84, c_349])).
% 3.85/1.73  tff(c_212, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.85/1.73  tff(c_220, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_212])).
% 3.85/1.73  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.85/1.73  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.85/1.73  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.73  tff(c_689, plain, (![A_225, B_226, C_227, D_228]: (k1_enumset1(A_225, B_226, C_227)=D_228 | k2_tarski(A_225, C_227)=D_228 | k2_tarski(B_226, C_227)=D_228 | k2_tarski(A_225, B_226)=D_228 | k1_tarski(C_227)=D_228 | k1_tarski(B_226)=D_228 | k1_tarski(A_225)=D_228 | k1_xboole_0=D_228 | ~r1_tarski(D_228, k1_enumset1(A_225, B_226, C_227)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.85/1.73  tff(c_717, plain, (![A_3, B_4, D_228]: (k1_enumset1(A_3, A_3, B_4)=D_228 | k2_tarski(A_3, B_4)=D_228 | k2_tarski(A_3, B_4)=D_228 | k2_tarski(A_3, A_3)=D_228 | k1_tarski(B_4)=D_228 | k1_tarski(A_3)=D_228 | k1_tarski(A_3)=D_228 | k1_xboole_0=D_228 | ~r1_tarski(D_228, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_689])).
% 3.85/1.73  tff(c_851, plain, (![A_282, B_283, D_284]: (k2_tarski(A_282, B_283)=D_284 | k2_tarski(A_282, B_283)=D_284 | k2_tarski(A_282, B_283)=D_284 | k1_tarski(A_282)=D_284 | k1_tarski(B_283)=D_284 | k1_tarski(A_282)=D_284 | k1_tarski(A_282)=D_284 | k1_xboole_0=D_284 | ~r1_tarski(D_284, k2_tarski(A_282, B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_717])).
% 3.85/1.73  tff(c_890, plain, (![A_285, B_286, B_287]: (k2_tarski(A_285, B_286)=k1_relat_1(B_287) | k1_tarski(B_286)=k1_relat_1(B_287) | k1_tarski(A_285)=k1_relat_1(B_287) | k1_relat_1(B_287)=k1_xboole_0 | ~v4_relat_1(B_287, k2_tarski(A_285, B_286)) | ~v1_relat_1(B_287))), inference(resolution, [status(thm)], [c_34, c_851])).
% 3.85/1.73  tff(c_897, plain, (![A_2, B_287]: (k2_tarski(A_2, A_2)=k1_relat_1(B_287) | k1_tarski(A_2)=k1_relat_1(B_287) | k1_tarski(A_2)=k1_relat_1(B_287) | k1_relat_1(B_287)=k1_xboole_0 | ~v4_relat_1(B_287, k1_tarski(A_2)) | ~v1_relat_1(B_287))), inference(superposition, [status(thm), theory('equality')], [c_4, c_890])).
% 3.85/1.73  tff(c_914, plain, (![A_292, B_293]: (k1_tarski(A_292)=k1_relat_1(B_293) | k1_tarski(A_292)=k1_relat_1(B_293) | k1_tarski(A_292)=k1_relat_1(B_293) | k1_relat_1(B_293)=k1_xboole_0 | ~v4_relat_1(B_293, k1_tarski(A_292)) | ~v1_relat_1(B_293))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_897])).
% 3.85/1.73  tff(c_920, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_220, c_914])).
% 3.85/1.73  tff(c_927, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_181, c_920])).
% 3.85/1.73  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_377, c_927])).
% 3.85/1.73  tff(c_930, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_190])).
% 3.85/1.73  tff(c_931, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_190])).
% 3.85/1.73  tff(c_946, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_930, c_931])).
% 3.85/1.73  tff(c_1106, plain, (![B_349, A_350]: (k1_tarski(k1_funct_1(B_349, A_350))=k2_relat_1(B_349) | k1_tarski(A_350)!=k1_relat_1(B_349) | ~v1_funct_1(B_349) | ~v1_relat_1(B_349))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.73  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.73  tff(c_938, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_28])).
% 3.85/1.73  tff(c_1084, plain, (![A_342, B_343, C_344]: (k2_relset_1(A_342, B_343, C_344)=k2_relat_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.85/1.73  tff(c_1089, plain, (![A_342, B_343]: (k2_relset_1(A_342, B_343, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_938, c_1084])).
% 3.85/1.73  tff(c_1090, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_76])).
% 3.85/1.73  tff(c_1112, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1106, c_1090])).
% 3.85/1.73  tff(c_1140, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_84, c_946, c_1112])).
% 3.85/1.73  tff(c_78, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.85/1.73  tff(c_940, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_930, c_78])).
% 3.85/1.73  tff(c_82, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.85/1.73  tff(c_74, plain, (![B_60, A_59, C_61]: (k1_xboole_0=B_60 | k1_relset_1(A_59, B_60, C_61)=A_59 | ~v1_funct_2(C_61, A_59, B_60) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.85/1.73  tff(c_1291, plain, (![B_377, A_378, C_379]: (B_377='#skF_6' | k1_relset_1(A_378, B_377, C_379)=A_378 | ~v1_funct_2(C_379, A_378, B_377) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_378, B_377))))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_74])).
% 3.85/1.73  tff(c_1298, plain, (![B_381, A_382]: (B_381='#skF_6' | k1_relset_1(A_382, B_381, '#skF_6')=A_382 | ~v1_funct_2('#skF_6', A_382, B_381))), inference(resolution, [status(thm)], [c_938, c_1291])).
% 3.85/1.73  tff(c_1310, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1298])).
% 3.85/1.73  tff(c_1318, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_940, c_1310])).
% 3.85/1.73  tff(c_58, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.85/1.73  tff(c_936, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | A_45='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_58])).
% 3.85/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.73  tff(c_939, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_2])).
% 3.85/1.73  tff(c_1337, plain, (![D_393, A_394, B_395, C_396]: (r2_hidden(k4_tarski(D_393, '#skF_2'(A_394, B_395, C_396, D_393)), C_396) | ~r2_hidden(D_393, B_395) | k1_relset_1(B_395, A_394, C_396)!=B_395 | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(B_395, A_394))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.85/1.73  tff(c_42, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.85/1.73  tff(c_1455, plain, (![C_423, D_424, A_425, B_426]: (~r1_tarski(C_423, k4_tarski(D_424, '#skF_2'(A_425, B_426, C_423, D_424))) | ~r2_hidden(D_424, B_426) | k1_relset_1(B_426, A_425, C_423)!=B_426 | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(B_426, A_425))))), inference(resolution, [status(thm)], [c_1337, c_42])).
% 3.85/1.73  tff(c_1463, plain, (![D_424, B_426, A_425]: (~r2_hidden(D_424, B_426) | k1_relset_1(B_426, A_425, '#skF_6')!=B_426 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_426, A_425))))), inference(resolution, [status(thm)], [c_939, c_1455])).
% 3.85/1.73  tff(c_1468, plain, (![D_427, B_428, A_429]: (~r2_hidden(D_427, B_428) | k1_relset_1(B_428, A_429, '#skF_6')!=B_428)), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1463])).
% 3.85/1.73  tff(c_1478, plain, (![A_430, A_431]: (k1_relset_1(A_430, A_431, '#skF_6')!=A_430 | A_430='#skF_6')), inference(resolution, [status(thm)], [c_936, c_1468])).
% 3.85/1.73  tff(c_1481, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1318, c_1478])).
% 3.85/1.73  tff(c_1488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1140, c_1481])).
% 3.85/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  Inference rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Ref     : 0
% 3.85/1.73  #Sup     : 279
% 3.85/1.73  #Fact    : 0
% 3.85/1.73  #Define  : 0
% 3.85/1.73  #Split   : 3
% 3.85/1.73  #Chain   : 0
% 3.85/1.73  #Close   : 0
% 3.85/1.73  
% 3.85/1.73  Ordering : KBO
% 3.85/1.73  
% 3.85/1.73  Simplification rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Subsume      : 39
% 3.85/1.73  #Demod        : 176
% 3.85/1.73  #Tautology    : 132
% 3.85/1.73  #SimpNegUnit  : 5
% 3.85/1.73  #BackRed      : 13
% 3.85/1.73  
% 3.85/1.73  #Partial instantiations: 0
% 3.85/1.73  #Strategies tried      : 1
% 3.85/1.73  
% 3.85/1.73  Timing (in seconds)
% 3.85/1.73  ----------------------
% 3.85/1.73  Preprocessing        : 0.38
% 3.85/1.73  Parsing              : 0.20
% 3.85/1.73  CNF conversion       : 0.03
% 3.85/1.73  Main loop            : 0.56
% 3.85/1.73  Inferencing          : 0.21
% 3.85/1.73  Reduction            : 0.17
% 3.85/1.73  Demodulation         : 0.12
% 3.85/1.73  BG Simplification    : 0.03
% 4.28/1.73  Subsumption          : 0.10
% 4.28/1.73  Abstraction          : 0.03
% 4.28/1.73  MUC search           : 0.00
% 4.28/1.73  Cooper               : 0.00
% 4.28/1.73  Total                : 0.98
% 4.28/1.73  Index Insertion      : 0.00
% 4.28/1.73  Index Deletion       : 0.00
% 4.28/1.73  Index Matching       : 0.00
% 4.28/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
