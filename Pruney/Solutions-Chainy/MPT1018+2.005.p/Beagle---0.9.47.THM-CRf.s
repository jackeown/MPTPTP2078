%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 187 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 599 expanded)
%              Number of equality atoms :   38 ( 159 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_26,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_311,plain,(
    ! [D_64,C_65,B_66,A_67] :
      ( k1_funct_1(k2_funct_1(D_64),k1_funct_1(D_64,C_65)) = C_65
      | k1_xboole_0 = B_66
      | ~ r2_hidden(C_65,A_67)
      | ~ v2_funct_1(D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66)))
      | ~ v1_funct_2(D_64,A_67,B_66)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_337,plain,(
    ! [D_71,B_72] :
      ( k1_funct_1(k2_funct_1(D_71),k1_funct_1(D_71,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_72
      | ~ v2_funct_1(D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_72)))
      | ~ v1_funct_2(D_71,'#skF_1',B_72)
      | ~ v1_funct_1(D_71) ) ),
    inference(resolution,[status(thm)],[c_32,c_311])).

tff(c_348,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_337])).

tff(c_354,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_28,c_348])).

tff(c_355,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_363,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_8])).

tff(c_112,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_142,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k1_relset_1(A_46,B_47,C_48),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_142])).

tff(c_161,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_179,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_179])).

tff(c_372,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_371,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_409,plain,(
    ! [D_77,B_78] :
      ( k1_funct_1(k2_funct_1(D_77),k1_funct_1(D_77,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_78
      | ~ v2_funct_1(D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_78)))
      | ~ v1_funct_2(D_77,'#skF_1',B_78)
      | ~ v1_funct_1(D_77) ) ),
    inference(resolution,[status(thm)],[c_30,c_311])).

tff(c_420,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_409])).

tff(c_426,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_371,c_420])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_26,c_426])).

tff(c_429,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_498,plain,(
    ! [B_86,A_87] :
      ( k1_funct_1(k2_funct_1(B_86),k1_funct_1(B_86,A_87)) = A_87
      | ~ r2_hidden(A_87,k1_relat_1(B_86))
      | ~ v2_funct_1(B_86)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_516,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_498])).

tff(c_520,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_34,c_32,c_429,c_516])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( k1_funct_1(k2_funct_1(B_7),k1_funct_1(B_7,A_6)) = A_6
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_595,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_16])).

tff(c_602,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_34,c_30,c_429,c_595])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:05:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.59  
% 2.87/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.59  
% 2.87/1.59  %Foreground sorts:
% 2.87/1.59  
% 2.87/1.59  
% 2.87/1.59  %Background operators:
% 2.87/1.59  
% 2.87/1.59  
% 2.87/1.59  %Foreground operators:
% 2.87/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.87/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.87/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.87/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.59  
% 2.87/1.60  tff(f_93, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 2.87/1.60  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.87/1.60  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 2.87/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.60  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.60  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.87/1.60  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.87/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.60  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 2.87/1.60  tff(c_26, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_84, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.60  tff(c_93, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_84])).
% 2.87/1.60  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_34, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_38, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_28, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.87/1.60  tff(c_311, plain, (![D_64, C_65, B_66, A_67]: (k1_funct_1(k2_funct_1(D_64), k1_funct_1(D_64, C_65))=C_65 | k1_xboole_0=B_66 | ~r2_hidden(C_65, A_67) | ~v2_funct_1(D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))) | ~v1_funct_2(D_64, A_67, B_66) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.60  tff(c_337, plain, (![D_71, B_72]: (k1_funct_1(k2_funct_1(D_71), k1_funct_1(D_71, '#skF_3'))='#skF_3' | k1_xboole_0=B_72 | ~v2_funct_1(D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_72))) | ~v1_funct_2(D_71, '#skF_1', B_72) | ~v1_funct_1(D_71))), inference(resolution, [status(thm)], [c_32, c_311])).
% 2.87/1.60  tff(c_348, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_337])).
% 2.87/1.60  tff(c_354, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_28, c_348])).
% 2.87/1.60  tff(c_355, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_354])).
% 2.87/1.60  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.60  tff(c_363, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_8])).
% 2.87/1.60  tff(c_112, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.60  tff(c_121, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.87/1.60  tff(c_142, plain, (![A_46, B_47, C_48]: (m1_subset_1(k1_relset_1(A_46, B_47, C_48), k1_zfmisc_1(A_46)) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.60  tff(c_156, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_121, c_142])).
% 2.87/1.60  tff(c_161, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_156])).
% 2.87/1.60  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.60  tff(c_165, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_161, c_10])).
% 2.87/1.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.60  tff(c_168, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_165, c_2])).
% 2.87/1.60  tff(c_179, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_168])).
% 2.87/1.60  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_363, c_179])).
% 2.87/1.60  tff(c_372, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_354])).
% 2.87/1.60  tff(c_371, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_354])).
% 2.87/1.60  tff(c_409, plain, (![D_77, B_78]: (k1_funct_1(k2_funct_1(D_77), k1_funct_1(D_77, '#skF_4'))='#skF_4' | k1_xboole_0=B_78 | ~v2_funct_1(D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_78))) | ~v1_funct_2(D_77, '#skF_1', B_78) | ~v1_funct_1(D_77))), inference(resolution, [status(thm)], [c_30, c_311])).
% 2.87/1.60  tff(c_420, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_409])).
% 2.87/1.60  tff(c_426, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_371, c_420])).
% 2.87/1.60  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_372, c_26, c_426])).
% 2.87/1.60  tff(c_429, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_168])).
% 2.87/1.60  tff(c_498, plain, (![B_86, A_87]: (k1_funct_1(k2_funct_1(B_86), k1_funct_1(B_86, A_87))=A_87 | ~r2_hidden(A_87, k1_relat_1(B_86)) | ~v2_funct_1(B_86) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.60  tff(c_516, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_498])).
% 2.87/1.60  tff(c_520, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_34, c_32, c_429, c_516])).
% 2.87/1.60  tff(c_16, plain, (![B_7, A_6]: (k1_funct_1(k2_funct_1(B_7), k1_funct_1(B_7, A_6))=A_6 | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.60  tff(c_595, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_520, c_16])).
% 2.87/1.60  tff(c_602, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_34, c_30, c_429, c_595])).
% 2.87/1.60  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_602])).
% 2.87/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.60  
% 2.87/1.60  Inference rules
% 2.87/1.60  ----------------------
% 2.87/1.60  #Ref     : 0
% 2.87/1.60  #Sup     : 121
% 2.87/1.60  #Fact    : 0
% 2.87/1.60  #Define  : 0
% 2.87/1.60  #Split   : 4
% 2.87/1.60  #Chain   : 0
% 2.87/1.60  #Close   : 0
% 2.87/1.60  
% 2.87/1.60  Ordering : KBO
% 2.87/1.60  
% 2.87/1.60  Simplification rules
% 2.87/1.60  ----------------------
% 2.87/1.60  #Subsume      : 2
% 2.87/1.60  #Demod        : 99
% 2.87/1.60  #Tautology    : 67
% 2.87/1.60  #SimpNegUnit  : 4
% 2.87/1.60  #BackRed      : 20
% 2.87/1.60  
% 2.87/1.60  #Partial instantiations: 0
% 2.87/1.60  #Strategies tried      : 1
% 2.87/1.60  
% 2.87/1.60  Timing (in seconds)
% 2.87/1.60  ----------------------
% 2.87/1.61  Preprocessing        : 0.44
% 2.87/1.61  Parsing              : 0.23
% 2.87/1.61  CNF conversion       : 0.03
% 2.87/1.61  Main loop            : 0.33
% 2.87/1.61  Inferencing          : 0.12
% 2.87/1.61  Reduction            : 0.10
% 2.87/1.61  Demodulation         : 0.08
% 2.87/1.61  BG Simplification    : 0.02
% 2.87/1.61  Subsumption          : 0.06
% 2.87/1.61  Abstraction          : 0.02
% 2.87/1.61  MUC search           : 0.00
% 2.87/1.61  Cooper               : 0.00
% 2.87/1.61  Total                : 0.80
% 2.87/1.61  Index Insertion      : 0.00
% 2.87/1.61  Index Deletion       : 0.00
% 2.87/1.61  Index Matching       : 0.00
% 2.87/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
