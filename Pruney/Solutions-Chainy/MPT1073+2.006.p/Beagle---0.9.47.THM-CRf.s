%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 266 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_65,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_87,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_11,C_47] :
      ( k1_funct_1(A_11,'#skF_4'(A_11,k2_relat_1(A_11),C_47)) = C_47
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [A_120,C_121] :
      ( r2_hidden('#skF_4'(A_120,k2_relat_1(A_120),C_121),k1_relat_1(A_120))
      | ~ r2_hidden(C_121,k2_relat_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_456,plain,(
    ! [A_157,C_158,A_159] :
      ( r2_hidden('#skF_4'(A_157,k2_relat_1(A_157),C_158),A_159)
      | ~ m1_subset_1(k1_relat_1(A_157),k1_zfmisc_1(A_159))
      | ~ r2_hidden(C_158,k2_relat_1(A_157))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_468,plain,(
    ! [A_160,C_161,A_162] :
      ( m1_subset_1('#skF_4'(A_160,k2_relat_1(A_160),C_161),A_162)
      | ~ m1_subset_1(k1_relat_1(A_160),k1_zfmisc_1(A_162))
      | ~ r2_hidden(C_161,k2_relat_1(A_160))
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_456,c_4])).

tff(c_40,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_5'
      | ~ m1_subset_1(E_61,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_532,plain,(
    ! [A_169,C_170] :
      ( k1_funct_1('#skF_8','#skF_4'(A_169,k2_relat_1(A_169),C_170)) != '#skF_5'
      | ~ m1_subset_1(k1_relat_1(A_169),k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(C_170,k2_relat_1(A_169))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(resolution,[status(thm)],[c_468,c_40])).

tff(c_535,plain,(
    ! [C_47] :
      ( C_47 != '#skF_5'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_532])).

tff(c_537,plain,(
    ! [C_47] :
      ( C_47 != '#skF_5'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_74,c_48,c_535])).

tff(c_538,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_542,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_538])).

tff(c_545,plain,
    ( ~ v4_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_542])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_96,c_545])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_146,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_155,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_146])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_159,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_42])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_569,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.39  
% 2.90/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.90/1.40  
% 2.90/1.40  %Foreground sorts:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Background operators:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Foreground operators:
% 2.90/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.90/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.90/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.90/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.90/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.40  
% 2.90/1.41  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.90/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.41  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.41  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.90/1.41  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.90/1.41  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.90/1.41  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.90/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.90/1.41  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.41  tff(c_65, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.41  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_65])).
% 2.90/1.41  tff(c_87, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.41  tff(c_96, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.90/1.41  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.90/1.41  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.90/1.41  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.41  tff(c_16, plain, (![A_11, C_47]: (k1_funct_1(A_11, '#skF_4'(A_11, k2_relat_1(A_11), C_47))=C_47 | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.41  tff(c_202, plain, (![A_120, C_121]: (r2_hidden('#skF_4'(A_120, k2_relat_1(A_120), C_121), k1_relat_1(A_120)) | ~r2_hidden(C_121, k2_relat_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.41  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.41  tff(c_456, plain, (![A_157, C_158, A_159]: (r2_hidden('#skF_4'(A_157, k2_relat_1(A_157), C_158), A_159) | ~m1_subset_1(k1_relat_1(A_157), k1_zfmisc_1(A_159)) | ~r2_hidden(C_158, k2_relat_1(A_157)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_202, c_2])).
% 2.90/1.41  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.41  tff(c_468, plain, (![A_160, C_161, A_162]: (m1_subset_1('#skF_4'(A_160, k2_relat_1(A_160), C_161), A_162) | ~m1_subset_1(k1_relat_1(A_160), k1_zfmisc_1(A_162)) | ~r2_hidden(C_161, k2_relat_1(A_160)) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_456, c_4])).
% 2.90/1.41  tff(c_40, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_5' | ~m1_subset_1(E_61, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.41  tff(c_532, plain, (![A_169, C_170]: (k1_funct_1('#skF_8', '#skF_4'(A_169, k2_relat_1(A_169), C_170))!='#skF_5' | ~m1_subset_1(k1_relat_1(A_169), k1_zfmisc_1('#skF_6')) | ~r2_hidden(C_170, k2_relat_1(A_169)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(resolution, [status(thm)], [c_468, c_40])).
% 2.90/1.41  tff(c_535, plain, (![C_47]: (C_47!='#skF_5' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_532])).
% 2.90/1.41  tff(c_537, plain, (![C_47]: (C_47!='#skF_5' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~r2_hidden(C_47, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_74, c_48, c_535])).
% 2.90/1.41  tff(c_538, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_537])).
% 2.90/1.41  tff(c_542, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_8, c_538])).
% 2.90/1.41  tff(c_545, plain, (~v4_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_542])).
% 2.90/1.41  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_96, c_545])).
% 2.90/1.41  tff(c_569, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_537])).
% 2.90/1.41  tff(c_146, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.41  tff(c_155, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_146])).
% 2.90/1.41  tff(c_42, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.41  tff(c_159, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_42])).
% 2.90/1.41  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_569, c_159])).
% 2.90/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.41  
% 2.90/1.41  Inference rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Ref     : 0
% 2.90/1.41  #Sup     : 114
% 2.90/1.41  #Fact    : 0
% 2.90/1.41  #Define  : 0
% 2.90/1.41  #Split   : 1
% 2.90/1.41  #Chain   : 0
% 2.90/1.41  #Close   : 0
% 2.90/1.41  
% 2.90/1.41  Ordering : KBO
% 2.90/1.41  
% 2.90/1.41  Simplification rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Subsume      : 4
% 2.90/1.41  #Demod        : 17
% 2.90/1.41  #Tautology    : 19
% 2.90/1.41  #SimpNegUnit  : 1
% 2.90/1.41  #BackRed      : 5
% 2.90/1.41  
% 2.90/1.41  #Partial instantiations: 0
% 2.90/1.41  #Strategies tried      : 1
% 2.90/1.41  
% 2.90/1.41  Timing (in seconds)
% 2.90/1.41  ----------------------
% 2.90/1.41  Preprocessing        : 0.32
% 2.90/1.41  Parsing              : 0.16
% 2.90/1.41  CNF conversion       : 0.03
% 2.90/1.41  Main loop            : 0.33
% 2.90/1.41  Inferencing          : 0.13
% 2.90/1.41  Reduction            : 0.08
% 2.90/1.41  Demodulation         : 0.06
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.07
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.68
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
