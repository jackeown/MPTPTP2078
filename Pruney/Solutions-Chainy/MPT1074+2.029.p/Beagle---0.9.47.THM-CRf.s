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
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 100 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  141 ( 332 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,B,C)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
          & ! [E] :
              ( m1_subset_1(E,B)
             => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_14,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_29] : r1_tarski(A_29,A_29) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_22,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_1,B_2,B_34] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_34)
      | ~ r1_tarski(A_1,B_34)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_64,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( m1_subset_1('#skF_2'(A_48,B_49,C_50,D_51),B_49)
      | ~ r2_hidden(A_48,k2_relset_1(B_49,C_50,D_51))
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(B_49,C_50)))
      | ~ v1_funct_2(D_51,B_49,C_50)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,(
    ! [B_49,B_2,A_1,D_51,C_50] :
      ( m1_subset_1('#skF_2'('#skF_1'(A_1,B_2),B_49,C_50,D_51),B_49)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(B_49,C_50)))
      | ~ v1_funct_2(D_51,B_49,C_50)
      | ~ v1_funct_1(D_51)
      | ~ r1_tarski(A_1,k2_relset_1(B_49,C_50,D_51))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_81,plain,(
    ! [D_56,A_57,B_58,C_59] :
      ( k1_funct_1(D_56,'#skF_2'(A_57,B_58,C_59,D_56)) = A_57
      | ~ r2_hidden(A_57,k2_relset_1(B_58,C_59,D_56))
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(B_58,C_59)))
      | ~ v1_funct_2(D_56,B_58,C_59)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [D_56,B_58,C_59,B_2] :
      ( k1_funct_1(D_56,'#skF_2'('#skF_1'(k2_relset_1(B_58,C_59,D_56),B_2),B_58,C_59,D_56)) = '#skF_1'(k2_relset_1(B_58,C_59,D_56),B_2)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(B_58,C_59)))
      | ~ v1_funct_2(D_56,B_58,C_59)
      | ~ v1_funct_1(D_56)
      | r1_tarski(k2_relset_1(B_58,C_59,D_56),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    ! [B_67,D_64,C_66,B_65,A_68] :
      ( m1_subset_1('#skF_2'('#skF_1'(A_68,B_67),B_65,C_66,D_64),B_65)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_65,C_66)))
      | ~ v1_funct_2(D_64,B_65,C_66)
      | ~ v1_funct_1(D_64)
      | ~ r1_tarski(A_68,k2_relset_1(B_65,C_66,D_64))
      | r1_tarski(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k3_funct_2(A_6,B_7,C_8,D_9) = k1_funct_1(C_8,D_9)
      | ~ m1_subset_1(D_9,A_6)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(C_8,A_6,B_7)
      | ~ v1_funct_1(C_8)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [A_102,D_99,B_103,B_101,B_97,C_100,C_98] :
      ( k3_funct_2(B_97,B_101,C_100,'#skF_2'('#skF_1'(A_102,B_103),B_97,C_98,D_99)) = k1_funct_1(C_100,'#skF_2'('#skF_1'(A_102,B_103),B_97,C_98,D_99))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(B_97,B_101)))
      | ~ v1_funct_2(C_100,B_97,B_101)
      | ~ v1_funct_1(C_100)
      | v1_xboole_0(B_97)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(B_97,C_98)))
      | ~ v1_funct_2(D_99,B_97,C_98)
      | ~ v1_funct_1(D_99)
      | ~ r1_tarski(A_102,k2_relset_1(B_97,C_98,D_99))
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_224,plain,(
    ! [A_102,B_103,C_98,D_99] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_1'(A_102,B_103),'#skF_4',C_98,D_99)) = k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_102,B_103),'#skF_4',C_98,D_99))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_98)))
      | ~ v1_funct_2(D_99,'#skF_4',C_98)
      | ~ v1_funct_1(D_99)
      | ~ r1_tarski(A_102,k2_relset_1('#skF_4',C_98,D_99))
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_18,c_213])).

tff(c_230,plain,(
    ! [A_102,B_103,C_98,D_99] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_1'(A_102,B_103),'#skF_4',C_98,D_99)) = k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_102,B_103),'#skF_4',C_98,D_99))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_98)))
      | ~ v1_funct_2(D_99,'#skF_4',C_98)
      | ~ v1_funct_1(D_99)
      | ~ r1_tarski(A_102,k2_relset_1('#skF_4',C_98,D_99))
      | r1_tarski(A_102,B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_224])).

tff(c_232,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_1'(A_104,B_105),'#skF_4',C_106,D_107)) = k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_104,B_105),'#skF_4',C_106,D_107))
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_106)))
      | ~ v1_funct_2(D_107,'#skF_4',C_106)
      | ~ v1_funct_1(D_107)
      | ~ r1_tarski(A_104,k2_relset_1('#skF_4',C_106,D_107))
      | r1_tarski(A_104,B_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_230])).

tff(c_243,plain,(
    ! [A_104,B_105] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_1'(A_104,B_105),'#skF_4','#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_104,B_105),'#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(A_104,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_18,c_232])).

tff(c_250,plain,(
    ! [A_108,B_109] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_1'(A_108,B_109),'#skF_4','#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_108,B_109),'#skF_4','#skF_5','#skF_6'))
      | ~ r1_tarski(A_108,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_108,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_243])).

tff(c_16,plain,(
    ! [E_26] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_26),'#skF_3')
      | ~ m1_subset_1(E_26,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_268,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_1'(A_110,B_111),'#skF_4','#skF_5','#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_1'(A_110,B_111),'#skF_4','#skF_5','#skF_6'),'#skF_4')
      | ~ r1_tarski(A_110,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_110,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_16])).

tff(c_274,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_4','#skF_5','#skF_6'),'#skF_4')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_268])).

tff(c_327,plain,(
    ! [B_118] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_118),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_118),'#skF_4','#skF_5','#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_33,c_274])).

tff(c_331,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(resolution,[status(thm)],[c_75,c_327])).

tff(c_342,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_119),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_22,c_20,c_18,c_331])).

tff(c_348,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_342,c_4])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_14,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:50:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.50  
% 2.82/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.50  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.82/1.50  
% 2.82/1.50  %Foreground sorts:
% 2.82/1.50  
% 2.82/1.50  
% 2.82/1.50  %Background operators:
% 2.82/1.50  
% 2.82/1.50  
% 2.82/1.50  %Foreground operators:
% 2.82/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.82/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.50  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.82/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.50  
% 2.82/1.52  tff(f_82, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 2.82/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.82/1.52  tff(f_60, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.82/1.52  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.82/1.52  tff(c_14, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_28, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.52  tff(c_33, plain, (![A_29]: (r1_tarski(A_29, A_29))), inference(resolution, [status(thm)], [c_28, c_4])).
% 2.82/1.52  tff(c_22, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_20, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_18, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.52  tff(c_36, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.52  tff(c_42, plain, (![A_1, B_2, B_34]: (r2_hidden('#skF_1'(A_1, B_2), B_34) | ~r1_tarski(A_1, B_34) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_36])).
% 2.82/1.52  tff(c_64, plain, (![A_48, B_49, C_50, D_51]: (m1_subset_1('#skF_2'(A_48, B_49, C_50, D_51), B_49) | ~r2_hidden(A_48, k2_relset_1(B_49, C_50, D_51)) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(B_49, C_50))) | ~v1_funct_2(D_51, B_49, C_50) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.52  tff(c_75, plain, (![B_49, B_2, A_1, D_51, C_50]: (m1_subset_1('#skF_2'('#skF_1'(A_1, B_2), B_49, C_50, D_51), B_49) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(B_49, C_50))) | ~v1_funct_2(D_51, B_49, C_50) | ~v1_funct_1(D_51) | ~r1_tarski(A_1, k2_relset_1(B_49, C_50, D_51)) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.82/1.52  tff(c_81, plain, (![D_56, A_57, B_58, C_59]: (k1_funct_1(D_56, '#skF_2'(A_57, B_58, C_59, D_56))=A_57 | ~r2_hidden(A_57, k2_relset_1(B_58, C_59, D_56)) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(B_58, C_59))) | ~v1_funct_2(D_56, B_58, C_59) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.52  tff(c_93, plain, (![D_56, B_58, C_59, B_2]: (k1_funct_1(D_56, '#skF_2'('#skF_1'(k2_relset_1(B_58, C_59, D_56), B_2), B_58, C_59, D_56))='#skF_1'(k2_relset_1(B_58, C_59, D_56), B_2) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(B_58, C_59))) | ~v1_funct_2(D_56, B_58, C_59) | ~v1_funct_1(D_56) | r1_tarski(k2_relset_1(B_58, C_59, D_56), B_2))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.82/1.52  tff(c_26, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_99, plain, (![B_67, D_64, C_66, B_65, A_68]: (m1_subset_1('#skF_2'('#skF_1'(A_68, B_67), B_65, C_66, D_64), B_65) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_65, C_66))) | ~v1_funct_2(D_64, B_65, C_66) | ~v1_funct_1(D_64) | ~r1_tarski(A_68, k2_relset_1(B_65, C_66, D_64)) | r1_tarski(A_68, B_67))), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.82/1.52  tff(c_8, plain, (![A_6, B_7, C_8, D_9]: (k3_funct_2(A_6, B_7, C_8, D_9)=k1_funct_1(C_8, D_9) | ~m1_subset_1(D_9, A_6) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(C_8, A_6, B_7) | ~v1_funct_1(C_8) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.52  tff(c_213, plain, (![A_102, D_99, B_103, B_101, B_97, C_100, C_98]: (k3_funct_2(B_97, B_101, C_100, '#skF_2'('#skF_1'(A_102, B_103), B_97, C_98, D_99))=k1_funct_1(C_100, '#skF_2'('#skF_1'(A_102, B_103), B_97, C_98, D_99)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(B_97, B_101))) | ~v1_funct_2(C_100, B_97, B_101) | ~v1_funct_1(C_100) | v1_xboole_0(B_97) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(B_97, C_98))) | ~v1_funct_2(D_99, B_97, C_98) | ~v1_funct_1(D_99) | ~r1_tarski(A_102, k2_relset_1(B_97, C_98, D_99)) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_99, c_8])).
% 2.82/1.52  tff(c_224, plain, (![A_102, B_103, C_98, D_99]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_1'(A_102, B_103), '#skF_4', C_98, D_99))=k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_102, B_103), '#skF_4', C_98, D_99)) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_98))) | ~v1_funct_2(D_99, '#skF_4', C_98) | ~v1_funct_1(D_99) | ~r1_tarski(A_102, k2_relset_1('#skF_4', C_98, D_99)) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_18, c_213])).
% 2.82/1.52  tff(c_230, plain, (![A_102, B_103, C_98, D_99]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_1'(A_102, B_103), '#skF_4', C_98, D_99))=k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_102, B_103), '#skF_4', C_98, D_99)) | v1_xboole_0('#skF_4') | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_98))) | ~v1_funct_2(D_99, '#skF_4', C_98) | ~v1_funct_1(D_99) | ~r1_tarski(A_102, k2_relset_1('#skF_4', C_98, D_99)) | r1_tarski(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_224])).
% 2.82/1.52  tff(c_232, plain, (![A_104, B_105, C_106, D_107]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_1'(A_104, B_105), '#skF_4', C_106, D_107))=k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_104, B_105), '#skF_4', C_106, D_107)) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_106))) | ~v1_funct_2(D_107, '#skF_4', C_106) | ~v1_funct_1(D_107) | ~r1_tarski(A_104, k2_relset_1('#skF_4', C_106, D_107)) | r1_tarski(A_104, B_105))), inference(negUnitSimplification, [status(thm)], [c_26, c_230])).
% 2.82/1.52  tff(c_243, plain, (![A_104, B_105]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_1'(A_104, B_105), '#skF_4', '#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_104, B_105), '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(A_104, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_18, c_232])).
% 2.82/1.52  tff(c_250, plain, (![A_108, B_109]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_1'(A_108, B_109), '#skF_4', '#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_108, B_109), '#skF_4', '#skF_5', '#skF_6')) | ~r1_tarski(A_108, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_108, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_243])).
% 2.82/1.52  tff(c_16, plain, (![E_26]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_26), '#skF_3') | ~m1_subset_1(E_26, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.52  tff(c_268, plain, (![A_110, B_111]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_1'(A_110, B_111), '#skF_4', '#skF_5', '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_1'(A_110, B_111), '#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~r1_tarski(A_110, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_110, B_111))), inference(superposition, [status(thm), theory('equality')], [c_250, c_16])).
% 2.82/1.52  tff(c_274, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_93, c_268])).
% 2.82/1.52  tff(c_327, plain, (![B_118]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_118), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_118), '#skF_4', '#skF_5', '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_118))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_33, c_274])).
% 2.82/1.52  tff(c_331, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(resolution, [status(thm)], [c_75, c_327])).
% 2.82/1.52  tff(c_342, plain, (![B_119]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_119), '#skF_3') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_119))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_22, c_20, c_18, c_331])).
% 2.82/1.52  tff(c_348, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_342, c_4])).
% 2.82/1.52  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_14, c_348])).
% 2.82/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.52  
% 2.82/1.52  Inference rules
% 2.82/1.52  ----------------------
% 2.82/1.52  #Ref     : 0
% 2.82/1.52  #Sup     : 67
% 2.82/1.52  #Fact    : 0
% 2.82/1.52  #Define  : 0
% 2.82/1.52  #Split   : 2
% 2.82/1.52  #Chain   : 0
% 2.82/1.52  #Close   : 0
% 2.82/1.52  
% 2.82/1.52  Ordering : KBO
% 2.82/1.52  
% 2.82/1.52  Simplification rules
% 2.82/1.52  ----------------------
% 2.82/1.52  #Subsume      : 4
% 2.82/1.52  #Demod        : 54
% 2.82/1.52  #Tautology    : 13
% 2.82/1.52  #SimpNegUnit  : 8
% 2.82/1.52  #BackRed      : 0
% 2.82/1.52  
% 2.82/1.52  #Partial instantiations: 0
% 2.82/1.52  #Strategies tried      : 1
% 2.82/1.52  
% 2.82/1.52  Timing (in seconds)
% 2.82/1.52  ----------------------
% 2.82/1.52  Preprocessing        : 0.33
% 2.82/1.52  Parsing              : 0.18
% 2.82/1.52  CNF conversion       : 0.03
% 2.82/1.52  Main loop            : 0.34
% 2.82/1.52  Inferencing          : 0.13
% 2.82/1.52  Reduction            : 0.09
% 2.82/1.52  Demodulation         : 0.07
% 2.82/1.52  BG Simplification    : 0.02
% 2.82/1.52  Subsumption          : 0.07
% 2.82/1.52  Abstraction          : 0.03
% 2.82/1.52  MUC search           : 0.00
% 2.82/1.52  Cooper               : 0.00
% 2.82/1.52  Total                : 0.70
% 2.82/1.52  Index Insertion      : 0.00
% 2.82/1.52  Index Deletion       : 0.00
% 2.82/1.52  Index Matching       : 0.00
% 2.82/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
