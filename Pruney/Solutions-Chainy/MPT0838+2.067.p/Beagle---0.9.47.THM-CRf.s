%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 244 expanded)
%              Number of leaves         :   35 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 492 expanded)
%              Number of equality atoms :   32 ( 101 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_529,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_538,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_529])).

tff(c_36,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_539,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_36])).

tff(c_22,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_431,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_437,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_431])).

tff(c_441,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_437])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_132,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_163,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_172,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [A_81,C_82,B_83] :
      ( m1_subset_1(A_81,C_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(C_82))
      | ~ r2_hidden(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_248,plain,(
    ! [A_89,B_90,A_91] :
      ( m1_subset_1(A_89,B_90)
      | ~ r2_hidden(A_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_10,c_218])).

tff(c_252,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93)
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_4,c_248])).

tff(c_225,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_234,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_225])).

tff(c_53,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_46,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_235,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_131])).

tff(c_279,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_235])).

tff(c_286,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_289,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_286])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_172,c_289])).

tff(c_294,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_308,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_24])).

tff(c_316,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2,c_308])).

tff(c_46,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_351,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_316,c_52])).

tff(c_360,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_36])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_66,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_350,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_316,c_66])).

tff(c_367,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_350])).

tff(c_318,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_332,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_414,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_332])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_414])).

tff(c_416,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_574,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_585,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_574])).

tff(c_589,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_585])).

tff(c_599,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_24])).

tff(c_607,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_2,c_599])).

tff(c_617,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_607,c_66])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.45  
% 2.74/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.46  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.85/1.46  
% 2.85/1.46  %Foreground sorts:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Background operators:
% 2.85/1.46  
% 2.85/1.46  
% 2.85/1.46  %Foreground operators:
% 2.85/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.46  
% 2.85/1.47  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.85/1.47  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.47  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.85/1.47  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.85/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.47  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.85/1.47  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.85/1.47  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.85/1.47  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.85/1.47  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.85/1.47  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.85/1.47  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.85/1.47  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.85/1.47  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.85/1.47  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.85/1.47  tff(c_529, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.47  tff(c_538, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_529])).
% 2.85/1.47  tff(c_36, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.85/1.47  tff(c_539, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_538, c_36])).
% 2.85/1.47  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.85/1.47  tff(c_431, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.47  tff(c_437, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_431])).
% 2.85/1.47  tff(c_441, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_437])).
% 2.85/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.85/1.47  tff(c_132, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.47  tff(c_138, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.85/1.47  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_138])).
% 2.85/1.47  tff(c_163, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.85/1.47  tff(c_172, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.85/1.47  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.47  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.47  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.47  tff(c_218, plain, (![A_81, C_82, B_83]: (m1_subset_1(A_81, C_82) | ~m1_subset_1(B_83, k1_zfmisc_1(C_82)) | ~r2_hidden(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.47  tff(c_248, plain, (![A_89, B_90, A_91]: (m1_subset_1(A_89, B_90) | ~r2_hidden(A_89, A_91) | ~r1_tarski(A_91, B_90))), inference(resolution, [status(thm)], [c_10, c_218])).
% 2.85/1.47  tff(c_252, plain, (![A_92, B_93]: (m1_subset_1('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_4, c_248])).
% 2.85/1.47  tff(c_225, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.85/1.47  tff(c_234, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_225])).
% 2.85/1.47  tff(c_53, plain, (![D_46]: (~r2_hidden(D_46, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_46, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.85/1.47  tff(c_58, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_53])).
% 2.85/1.47  tff(c_131, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 2.85/1.47  tff(c_235, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_131])).
% 2.85/1.47  tff(c_279, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_252, c_235])).
% 2.85/1.47  tff(c_286, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_279])).
% 2.85/1.47  tff(c_289, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_286])).
% 2.85/1.47  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_172, c_289])).
% 2.85/1.47  tff(c_294, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_279])).
% 2.85/1.47  tff(c_24, plain, (![A_18]: (~v1_xboole_0(k2_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.47  tff(c_308, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_294, c_24])).
% 2.85/1.47  tff(c_316, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2, c_308])).
% 2.85/1.47  tff(c_46, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.85/1.47  tff(c_52, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_2, c_46])).
% 2.85/1.47  tff(c_351, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_316, c_52])).
% 2.85/1.47  tff(c_360, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_36])).
% 2.85/1.47  tff(c_20, plain, (![A_15]: (v1_xboole_0(k1_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.85/1.47  tff(c_59, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_2, c_46])).
% 2.85/1.47  tff(c_66, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_20, c_59])).
% 2.85/1.47  tff(c_350, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_316, c_66])).
% 2.85/1.47  tff(c_367, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_350])).
% 2.85/1.47  tff(c_318, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.47  tff(c_332, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_318])).
% 2.85/1.47  tff(c_414, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_332])).
% 2.85/1.47  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_414])).
% 2.85/1.47  tff(c_416, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 2.85/1.47  tff(c_574, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.85/1.47  tff(c_585, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_574])).
% 2.85/1.47  tff(c_589, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_416, c_585])).
% 2.85/1.47  tff(c_599, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_589, c_24])).
% 2.85/1.47  tff(c_607, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_2, c_599])).
% 2.85/1.47  tff(c_617, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_607, c_66])).
% 2.85/1.47  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_539, c_617])).
% 2.85/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  
% 2.85/1.47  Inference rules
% 2.85/1.47  ----------------------
% 2.85/1.47  #Ref     : 0
% 2.85/1.47  #Sup     : 127
% 2.85/1.47  #Fact    : 0
% 2.85/1.47  #Define  : 0
% 2.85/1.47  #Split   : 2
% 2.85/1.47  #Chain   : 0
% 2.85/1.47  #Close   : 0
% 2.85/1.47  
% 2.85/1.47  Ordering : KBO
% 2.85/1.47  
% 2.85/1.47  Simplification rules
% 2.85/1.47  ----------------------
% 2.85/1.47  #Subsume      : 6
% 2.85/1.47  #Demod        : 64
% 2.85/1.47  #Tautology    : 42
% 2.85/1.47  #SimpNegUnit  : 2
% 2.85/1.47  #BackRed      : 16
% 2.85/1.47  
% 2.85/1.47  #Partial instantiations: 0
% 2.85/1.47  #Strategies tried      : 1
% 2.85/1.47  
% 2.85/1.47  Timing (in seconds)
% 2.85/1.47  ----------------------
% 2.85/1.48  Preprocessing        : 0.33
% 2.85/1.48  Parsing              : 0.18
% 2.85/1.48  CNF conversion       : 0.02
% 2.85/1.48  Main loop            : 0.32
% 2.85/1.48  Inferencing          : 0.12
% 2.85/1.48  Reduction            : 0.09
% 2.85/1.48  Demodulation         : 0.06
% 2.85/1.48  BG Simplification    : 0.02
% 2.85/1.48  Subsumption          : 0.05
% 2.85/1.48  Abstraction          : 0.02
% 2.85/1.48  MUC search           : 0.00
% 2.85/1.48  Cooper               : 0.00
% 2.85/1.48  Total                : 0.69
% 2.85/1.48  Index Insertion      : 0.00
% 2.85/1.48  Index Deletion       : 0.00
% 2.85/1.48  Index Matching       : 0.00
% 2.85/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
