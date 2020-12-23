%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 165 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 332 expanded)
%              Number of equality atoms :   24 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_193,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_202,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_193])).

tff(c_203,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_32])).

tff(c_89,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_71,C_72,B_73] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_186,plain,(
    ! [A_85,B_86,A_87] :
      ( m1_subset_1(A_85,B_86)
      | ~ r2_hidden(A_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_215,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_156,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_156])).

tff(c_56,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_61,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_166,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_110])).

tff(c_247,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_215,c_166])).

tff(c_254,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_257,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_98,c_257])).

tff(c_262,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_139,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),k1_relat_1(B_75))
      | ~ r2_hidden(A_74,k2_relat_1(B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(k1_relat_1(B_77))
      | ~ r2_hidden(A_78,k2_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_151,plain,(
    ! [B_79] :
      ( ~ v1_xboole_0(k1_relat_1(B_79))
      | ~ v1_relat_1(B_79)
      | v1_xboole_0(k2_relat_1(B_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [B_79] :
      ( k2_relat_1(B_79) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_151,c_6])).

tff(c_266,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_262,c_155])).

tff(c_272,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_266])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_272])).

tff(c_275,plain,(
    v1_xboole_0(k1_relset_1('#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_290,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_6])).

tff(c_291,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_275])).

tff(c_345,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_352,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_345])).

tff(c_355,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_352])).

tff(c_328,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),k1_relat_1(B_105))
      | ~ r2_hidden(A_104,k2_relat_1(B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_334,plain,(
    ! [B_107,A_108] :
      ( ~ v1_xboole_0(k1_relat_1(B_107))
      | ~ r2_hidden(A_108,k2_relat_1(B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_328,c_2])).

tff(c_340,plain,(
    ! [B_109] :
      ( ~ v1_xboole_0(k1_relat_1(B_109))
      | ~ v1_relat_1(B_109)
      | v1_xboole_0(k2_relat_1(B_109)) ) ),
    inference(resolution,[status(thm)],[c_4,c_334])).

tff(c_385,plain,(
    ! [B_115] :
      ( k2_relat_1(B_115) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_340,c_6])).

tff(c_388,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_385])).

tff(c_390,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_291,c_388])).

tff(c_391,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_400,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_391])).

tff(c_422,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_400])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.60/1.37  
% 2.60/1.37  %Foreground sorts:
% 2.60/1.37  
% 2.60/1.37  
% 2.60/1.37  %Background operators:
% 2.60/1.37  
% 2.60/1.37  
% 2.60/1.37  %Foreground operators:
% 2.60/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.60/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.60/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.60/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.60/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.60/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.37  
% 2.60/1.39  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.60/1.39  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.60/1.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.60/1.39  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.60/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.60/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.60/1.39  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.60/1.39  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.60/1.39  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.60/1.39  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 2.60/1.39  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.39  tff(c_32, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.60/1.39  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.60/1.39  tff(c_62, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.39  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.60/1.39  tff(c_193, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.60/1.39  tff(c_202, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_193])).
% 2.60/1.39  tff(c_203, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_32])).
% 2.60/1.39  tff(c_89, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.39  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_89])).
% 2.60/1.39  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.39  tff(c_132, plain, (![A_71, C_72, B_73]: (m1_subset_1(A_71, C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.39  tff(c_186, plain, (![A_85, B_86, A_87]: (m1_subset_1(A_85, B_86) | ~r2_hidden(A_85, A_87) | ~r1_tarski(A_87, B_86))), inference(resolution, [status(thm)], [c_10, c_132])).
% 2.60/1.39  tff(c_215, plain, (![A_92, B_93]: (m1_subset_1('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_4, c_186])).
% 2.60/1.39  tff(c_156, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.39  tff(c_165, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_156])).
% 2.60/1.39  tff(c_56, plain, (![D_48]: (~r2_hidden(D_48, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.60/1.39  tff(c_61, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.60/1.39  tff(c_110, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.60/1.39  tff(c_166, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_110])).
% 2.60/1.39  tff(c_247, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_215, c_166])).
% 2.60/1.39  tff(c_254, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_247])).
% 2.60/1.39  tff(c_257, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_254])).
% 2.60/1.39  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_98, c_257])).
% 2.60/1.39  tff(c_262, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_247])).
% 2.60/1.39  tff(c_139, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), k1_relat_1(B_75)) | ~r2_hidden(A_74, k2_relat_1(B_75)) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_145, plain, (![B_77, A_78]: (~v1_xboole_0(k1_relat_1(B_77)) | ~r2_hidden(A_78, k2_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_139, c_2])).
% 2.60/1.39  tff(c_151, plain, (![B_79]: (~v1_xboole_0(k1_relat_1(B_79)) | ~v1_relat_1(B_79) | v1_xboole_0(k2_relat_1(B_79)))), inference(resolution, [status(thm)], [c_4, c_145])).
% 2.60/1.39  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.39  tff(c_155, plain, (![B_79]: (k2_relat_1(B_79)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_151, c_6])).
% 2.60/1.39  tff(c_266, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_262, c_155])).
% 2.60/1.39  tff(c_272, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_266])).
% 2.60/1.39  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_272])).
% 2.60/1.39  tff(c_275, plain, (v1_xboole_0(k1_relset_1('#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_61])).
% 2.60/1.39  tff(c_290, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_275, c_6])).
% 2.60/1.39  tff(c_291, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_275])).
% 2.60/1.39  tff(c_345, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.39  tff(c_352, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_345])).
% 2.60/1.39  tff(c_355, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_290, c_352])).
% 2.60/1.39  tff(c_328, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), k1_relat_1(B_105)) | ~r2_hidden(A_104, k2_relat_1(B_105)) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.39  tff(c_334, plain, (![B_107, A_108]: (~v1_xboole_0(k1_relat_1(B_107)) | ~r2_hidden(A_108, k2_relat_1(B_107)) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_328, c_2])).
% 2.60/1.39  tff(c_340, plain, (![B_109]: (~v1_xboole_0(k1_relat_1(B_109)) | ~v1_relat_1(B_109) | v1_xboole_0(k2_relat_1(B_109)))), inference(resolution, [status(thm)], [c_4, c_334])).
% 2.60/1.39  tff(c_385, plain, (![B_115]: (k2_relat_1(B_115)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(B_115)) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_340, c_6])).
% 2.60/1.39  tff(c_388, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_355, c_385])).
% 2.60/1.39  tff(c_390, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_291, c_388])).
% 2.60/1.39  tff(c_391, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.60/1.39  tff(c_400, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_391])).
% 2.60/1.39  tff(c_422, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_390, c_400])).
% 2.60/1.39  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_422])).
% 2.60/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  Inference rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Ref     : 0
% 2.60/1.39  #Sup     : 77
% 2.60/1.39  #Fact    : 0
% 2.60/1.39  #Define  : 0
% 2.60/1.39  #Split   : 3
% 2.60/1.39  #Chain   : 0
% 2.60/1.39  #Close   : 0
% 2.60/1.39  
% 2.60/1.39  Ordering : KBO
% 2.60/1.39  
% 2.60/1.39  Simplification rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Subsume      : 2
% 2.60/1.39  #Demod        : 30
% 2.60/1.39  #Tautology    : 22
% 2.60/1.39  #SimpNegUnit  : 2
% 2.60/1.39  #BackRed      : 5
% 2.60/1.39  
% 2.60/1.39  #Partial instantiations: 0
% 2.60/1.39  #Strategies tried      : 1
% 2.60/1.39  
% 2.60/1.39  Timing (in seconds)
% 2.60/1.39  ----------------------
% 2.60/1.39  Preprocessing        : 0.33
% 2.60/1.39  Parsing              : 0.18
% 2.60/1.39  CNF conversion       : 0.02
% 2.60/1.39  Main loop            : 0.24
% 2.60/1.39  Inferencing          : 0.10
% 2.60/1.39  Reduction            : 0.07
% 2.60/1.39  Demodulation         : 0.05
% 2.60/1.39  BG Simplification    : 0.01
% 2.60/1.39  Subsumption          : 0.04
% 2.60/1.39  Abstraction          : 0.01
% 2.60/1.39  MUC search           : 0.00
% 2.60/1.39  Cooper               : 0.00
% 2.60/1.39  Total                : 0.61
% 2.60/1.39  Index Insertion      : 0.00
% 2.60/1.39  Index Deletion       : 0.00
% 2.60/1.39  Index Matching       : 0.00
% 2.60/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
