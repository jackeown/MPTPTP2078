%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:03 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 248 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_28,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_106,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_102])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_761,plain,(
    ! [B_199,A_200] :
      ( m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_199),A_200)))
      | ~ r1_tarski(k2_relat_1(B_199),A_200)
      | ~ v1_funct_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k7_relset_1(A_47,B_48,C_49,D_50) = k9_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1113,plain,(
    ! [B_261,A_262,D_263] :
      ( k7_relset_1(k1_relat_1(B_261),A_262,B_261,D_263) = k9_relat_1(B_261,D_263)
      | ~ r1_tarski(k2_relat_1(B_261),A_262)
      | ~ v1_funct_1(B_261)
      | ~ v1_relat_1(B_261) ) ),
    inference(resolution,[status(thm)],[c_761,c_36])).

tff(c_1221,plain,(
    ! [B_272,D_273] :
      ( k7_relset_1(k1_relat_1(B_272),k2_relat_1(B_272),B_272,D_273) = k9_relat_1(B_272,D_273)
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272) ) ),
    inference(resolution,[status(thm)],[c_6,c_1113])).

tff(c_245,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( m1_subset_1(k7_relset_1(A_112,B_113,C_114,D_115),k1_zfmisc_1(B_113))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r1_tarski(k7_relset_1(A_112,B_113,C_114,D_115),B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_245,c_22])).

tff(c_783,plain,(
    ! [B_199,A_200,D_115] :
      ( r1_tarski(k7_relset_1(k1_relat_1(B_199),A_200,B_199,D_115),A_200)
      | ~ r1_tarski(k2_relat_1(B_199),A_200)
      | ~ v1_funct_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_761,c_273])).

tff(c_1227,plain,(
    ! [B_272,D_273] :
      ( r1_tarski(k9_relat_1(B_272,D_273),k2_relat_1(B_272))
      | ~ r1_tarski(k2_relat_1(B_272),k2_relat_1(B_272))
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272)
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_783])).

tff(c_1241,plain,(
    ! [B_274,D_275] :
      ( r1_tarski(k9_relat_1(B_274,D_275),k2_relat_1(B_274))
      | ~ v1_funct_1(B_274)
      | ~ v1_relat_1(B_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1227])).

tff(c_341,plain,(
    ! [B_128,A_129] :
      ( k1_tarski(k1_funct_1(B_128,A_129)) = k2_relat_1(B_128)
      | k1_tarski(A_129) != k1_relat_1(B_128)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,(
    ! [D_99] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_99) = k9_relat_1('#skF_4',D_99) ),
    inference(resolution,[status(thm)],[c_60,c_197])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_205,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_56])).

tff(c_347,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_205])).

tff(c_353,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_64,c_347])).

tff(c_378,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_153,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_162,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_153])).

tff(c_623,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_637,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_623])).

tff(c_643,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_162,c_637])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_58,c_643])).

tff(c_646,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_1244,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_646])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_64,c_1244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:49:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.55  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.52/1.55  
% 3.52/1.55  %Foreground sorts:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Background operators:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Foreground operators:
% 3.52/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.55  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.52/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.55  
% 3.63/1.56  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.63/1.56  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.63/1.56  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.63/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.56  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.63/1.56  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.63/1.56  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.63/1.56  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.63/1.56  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.63/1.56  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.63/1.56  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.63/1.56  tff(c_28, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.56  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.56  tff(c_96, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.63/1.56  tff(c_102, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_96])).
% 3.63/1.56  tff(c_106, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_102])).
% 3.63/1.56  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.56  tff(c_761, plain, (![B_199, A_200]: (m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_199), A_200))) | ~r1_tarski(k2_relat_1(B_199), A_200) | ~v1_funct_1(B_199) | ~v1_relat_1(B_199))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.63/1.56  tff(c_36, plain, (![A_47, B_48, C_49, D_50]: (k7_relset_1(A_47, B_48, C_49, D_50)=k9_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.63/1.56  tff(c_1113, plain, (![B_261, A_262, D_263]: (k7_relset_1(k1_relat_1(B_261), A_262, B_261, D_263)=k9_relat_1(B_261, D_263) | ~r1_tarski(k2_relat_1(B_261), A_262) | ~v1_funct_1(B_261) | ~v1_relat_1(B_261))), inference(resolution, [status(thm)], [c_761, c_36])).
% 3.63/1.56  tff(c_1221, plain, (![B_272, D_273]: (k7_relset_1(k1_relat_1(B_272), k2_relat_1(B_272), B_272, D_273)=k9_relat_1(B_272, D_273) | ~v1_funct_1(B_272) | ~v1_relat_1(B_272))), inference(resolution, [status(thm)], [c_6, c_1113])).
% 3.63/1.56  tff(c_245, plain, (![A_112, B_113, C_114, D_115]: (m1_subset_1(k7_relset_1(A_112, B_113, C_114, D_115), k1_zfmisc_1(B_113)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.63/1.56  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.56  tff(c_273, plain, (![A_112, B_113, C_114, D_115]: (r1_tarski(k7_relset_1(A_112, B_113, C_114, D_115), B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(resolution, [status(thm)], [c_245, c_22])).
% 3.63/1.56  tff(c_783, plain, (![B_199, A_200, D_115]: (r1_tarski(k7_relset_1(k1_relat_1(B_199), A_200, B_199, D_115), A_200) | ~r1_tarski(k2_relat_1(B_199), A_200) | ~v1_funct_1(B_199) | ~v1_relat_1(B_199))), inference(resolution, [status(thm)], [c_761, c_273])).
% 3.63/1.56  tff(c_1227, plain, (![B_272, D_273]: (r1_tarski(k9_relat_1(B_272, D_273), k2_relat_1(B_272)) | ~r1_tarski(k2_relat_1(B_272), k2_relat_1(B_272)) | ~v1_funct_1(B_272) | ~v1_relat_1(B_272) | ~v1_funct_1(B_272) | ~v1_relat_1(B_272))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_783])).
% 3.63/1.56  tff(c_1241, plain, (![B_274, D_275]: (r1_tarski(k9_relat_1(B_274, D_275), k2_relat_1(B_274)) | ~v1_funct_1(B_274) | ~v1_relat_1(B_274))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1227])).
% 3.63/1.56  tff(c_341, plain, (![B_128, A_129]: (k1_tarski(k1_funct_1(B_128, A_129))=k2_relat_1(B_128) | k1_tarski(A_129)!=k1_relat_1(B_128) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.63/1.56  tff(c_197, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.63/1.56  tff(c_204, plain, (![D_99]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_99)=k9_relat_1('#skF_4', D_99))), inference(resolution, [status(thm)], [c_60, c_197])).
% 3.63/1.56  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.56  tff(c_205, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_56])).
% 3.63/1.56  tff(c_347, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_341, c_205])).
% 3.63/1.56  tff(c_353, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_64, c_347])).
% 3.63/1.56  tff(c_378, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_353])).
% 3.63/1.56  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.56  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.56  tff(c_153, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.63/1.56  tff(c_162, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_153])).
% 3.63/1.56  tff(c_623, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.63/1.56  tff(c_637, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_60, c_623])).
% 3.63/1.56  tff(c_643, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_162, c_637])).
% 3.63/1.56  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_58, c_643])).
% 3.63/1.56  tff(c_646, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_353])).
% 3.63/1.56  tff(c_1244, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1241, c_646])).
% 3.63/1.56  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_64, c_1244])).
% 3.63/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.56  
% 3.63/1.56  Inference rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Ref     : 0
% 3.63/1.56  #Sup     : 247
% 3.63/1.56  #Fact    : 0
% 3.63/1.56  #Define  : 0
% 3.63/1.56  #Split   : 3
% 3.63/1.56  #Chain   : 0
% 3.63/1.56  #Close   : 0
% 3.63/1.56  
% 3.63/1.56  Ordering : KBO
% 3.63/1.56  
% 3.63/1.56  Simplification rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Subsume      : 25
% 3.63/1.56  #Demod        : 75
% 3.63/1.56  #Tautology    : 79
% 3.63/1.56  #SimpNegUnit  : 5
% 3.63/1.56  #BackRed      : 8
% 3.63/1.56  
% 3.63/1.56  #Partial instantiations: 0
% 3.63/1.56  #Strategies tried      : 1
% 3.63/1.56  
% 3.63/1.56  Timing (in seconds)
% 3.63/1.56  ----------------------
% 3.63/1.57  Preprocessing        : 0.34
% 3.63/1.57  Parsing              : 0.18
% 3.63/1.57  CNF conversion       : 0.02
% 3.63/1.57  Main loop            : 0.45
% 3.63/1.57  Inferencing          : 0.17
% 3.63/1.57  Reduction            : 0.13
% 3.63/1.57  Demodulation         : 0.09
% 3.63/1.57  BG Simplification    : 0.03
% 3.63/1.57  Subsumption          : 0.08
% 3.63/1.57  Abstraction          : 0.03
% 3.63/1.57  MUC search           : 0.00
% 3.63/1.57  Cooper               : 0.00
% 3.63/1.57  Total                : 0.82
% 3.63/1.57  Index Insertion      : 0.00
% 3.63/1.57  Index Deletion       : 0.00
% 3.63/1.57  Index Matching       : 0.00
% 3.63/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
