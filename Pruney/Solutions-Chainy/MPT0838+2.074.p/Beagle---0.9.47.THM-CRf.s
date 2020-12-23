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
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 216 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_71,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_67])).

tff(c_99,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_99])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) = k1_xboole_0
      | k2_relat_1(A_13) != k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_18])).

tff(c_80,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_215,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_201])).

tff(c_193,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_73)
      | k1_xboole_0 = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [D_34] :
      ( ~ r2_hidden(D_34,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_34,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_198,plain,(
    ! [A_72] :
      ( ~ m1_subset_1('#skF_1'(A_72,k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_193,c_30])).

tff(c_249,plain,(
    ! [A_72] :
      ( ~ m1_subset_1('#skF_1'(A_72,k2_relat_1('#skF_4')),'#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_215,c_198])).

tff(c_251,plain,(
    ! [A_87] :
      ( ~ m1_subset_1('#skF_1'(A_87,k2_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_87)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_249])).

tff(c_255,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_251])).

tff(c_258,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_255])).

tff(c_262,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_258])).

tff(c_265,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_262])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_108,c_265])).

tff(c_270,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_436,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_447,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_436])).

tff(c_451,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_447])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.49/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.36  
% 2.49/1.37  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.49/1.37  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.49/1.37  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.49/1.37  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.49/1.37  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.49/1.37  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.49/1.37  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.49/1.37  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.49/1.37  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.49/1.37  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.49/1.37  tff(c_32, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.49/1.37  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.37  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.49/1.37  tff(c_61, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.37  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.49/1.37  tff(c_71, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_67])).
% 2.49/1.37  tff(c_99, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.37  tff(c_108, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_99])).
% 2.49/1.37  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.37  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.37  tff(c_18, plain, (![A_13]: (k1_relat_1(A_13)=k1_xboole_0 | k2_relat_1(A_13)!=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.49/1.37  tff(c_78, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_18])).
% 2.49/1.37  tff(c_80, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 2.49/1.37  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.37  tff(c_201, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.49/1.37  tff(c_215, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_201])).
% 2.49/1.37  tff(c_193, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), B_73) | k1_xboole_0=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.37  tff(c_30, plain, (![D_34]: (~r2_hidden(D_34, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_34, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.49/1.37  tff(c_198, plain, (![A_72]: (~m1_subset_1('#skF_1'(A_72, k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_193, c_30])).
% 2.49/1.37  tff(c_249, plain, (![A_72]: (~m1_subset_1('#skF_1'(A_72, k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_215, c_198])).
% 2.49/1.37  tff(c_251, plain, (![A_87]: (~m1_subset_1('#skF_1'(A_87, k2_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_87)))), inference(negUnitSimplification, [status(thm)], [c_80, c_249])).
% 2.49/1.37  tff(c_255, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_251])).
% 2.49/1.37  tff(c_258, plain, (~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_255])).
% 2.49/1.37  tff(c_262, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_258])).
% 2.49/1.37  tff(c_265, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_262])).
% 2.49/1.37  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_108, c_265])).
% 2.49/1.37  tff(c_270, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 2.49/1.37  tff(c_436, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.37  tff(c_447, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_436])).
% 2.49/1.37  tff(c_451, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_270, c_447])).
% 2.49/1.37  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_451])).
% 2.49/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  Inference rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Ref     : 0
% 2.49/1.37  #Sup     : 80
% 2.49/1.37  #Fact    : 0
% 2.49/1.37  #Define  : 0
% 2.49/1.37  #Split   : 3
% 2.49/1.37  #Chain   : 0
% 2.49/1.37  #Close   : 0
% 2.49/1.37  
% 2.49/1.37  Ordering : KBO
% 2.49/1.37  
% 2.49/1.37  Simplification rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Subsume      : 4
% 2.49/1.37  #Demod        : 32
% 2.49/1.37  #Tautology    : 25
% 2.49/1.37  #SimpNegUnit  : 5
% 2.49/1.37  #BackRed      : 2
% 2.49/1.37  
% 2.49/1.37  #Partial instantiations: 0
% 2.49/1.37  #Strategies tried      : 1
% 2.49/1.37  
% 2.49/1.37  Timing (in seconds)
% 2.49/1.37  ----------------------
% 2.49/1.38  Preprocessing        : 0.29
% 2.49/1.38  Parsing              : 0.15
% 2.49/1.38  CNF conversion       : 0.02
% 2.49/1.38  Main loop            : 0.26
% 2.49/1.38  Inferencing          : 0.10
% 2.49/1.38  Reduction            : 0.07
% 2.49/1.38  Demodulation         : 0.05
% 2.49/1.38  BG Simplification    : 0.01
% 2.49/1.38  Subsumption          : 0.04
% 2.49/1.38  Abstraction          : 0.02
% 2.49/1.38  MUC search           : 0.00
% 2.49/1.38  Cooper               : 0.00
% 2.49/1.38  Total                : 0.58
% 2.49/1.38  Index Insertion      : 0.00
% 2.49/1.38  Index Deletion       : 0.00
% 2.49/1.38  Index Matching       : 0.00
% 2.49/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
