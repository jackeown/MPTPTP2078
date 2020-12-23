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
% DateTime   : Thu Dec  3 10:19:36 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 107 expanded)
%              Number of leaves         :   39 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 242 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_78,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_76,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_74,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_117,plain,(
    ! [A_91,B_92] :
      ( k6_domain_1(A_91,B_92) = k1_tarski(B_92)
      | ~ m1_subset_1(B_92,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_117])).

tff(c_122,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_56,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_56])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_125])).

tff(c_131,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_131])).

tff(c_136,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_203,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_119),B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_211,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_203])).

tff(c_215,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_211])).

tff(c_216,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_215])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [A_98,D_100,B_99,C_97,E_101] : k4_enumset1(A_98,A_98,B_99,C_97,D_100,E_101) = k3_enumset1(A_98,B_99,C_97,D_100,E_101) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [H_25,C_18,B_17,A_16,D_19,F_21] : r2_hidden(H_25,k4_enumset1(A_16,B_17,C_18,D_19,H_25,F_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [C_104,B_103,A_105,E_102,D_106] : r2_hidden(D_106,k3_enumset1(A_105,B_103,C_104,D_106,E_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_16])).

tff(c_190,plain,(
    ! [C_109,A_110,B_111,D_112] : r2_hidden(C_109,k2_enumset1(A_110,B_111,C_109,D_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_194,plain,(
    ! [B_113,A_114,C_115] : r2_hidden(B_113,k1_enumset1(A_114,B_113,C_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_198,plain,(
    ! [A_116,B_117] : r2_hidden(A_116,k2_tarski(A_116,B_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_201,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_198])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_138,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_68])).

tff(c_415,plain,(
    ! [B_227,A_228,C_229] :
      ( ~ r2_hidden(B_227,k1_orders_2(A_228,C_229))
      | ~ r2_hidden(B_227,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(B_227,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228)
      | ~ v5_orders_2(A_228)
      | ~ v4_orders_2(A_228)
      | ~ v3_orders_2(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_417,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_415])).

tff(c_420,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_216,c_201,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.46  
% 2.93/1.46  %Foreground sorts:
% 2.93/1.46  
% 2.93/1.46  
% 2.93/1.46  %Background operators:
% 2.93/1.46  
% 2.93/1.46  
% 2.93/1.46  %Foreground operators:
% 2.93/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.93/1.46  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.93/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.93/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.93/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.93/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.93/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.46  
% 3.05/1.48  tff(f_138, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 3.05/1.48  tff(f_77, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.05/1.48  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.05/1.48  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.05/1.48  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 3.05/1.48  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.05/1.48  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.05/1.48  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.05/1.48  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.05/1.48  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.05/1.48  tff(f_59, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.05/1.48  tff(f_120, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 3.05/1.48  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_78, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_76, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_74, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_72, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_70, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_58, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.05/1.48  tff(c_117, plain, (![A_91, B_92]: (k6_domain_1(A_91, B_92)=k1_tarski(B_92) | ~m1_subset_1(B_92, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.05/1.48  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_117])).
% 3.05/1.48  tff(c_122, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_121])).
% 3.05/1.48  tff(c_56, plain, (![A_29]: (~v1_xboole_0(u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.48  tff(c_125, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_122, c_56])).
% 3.05/1.48  tff(c_128, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_125])).
% 3.05/1.48  tff(c_131, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_58, c_128])).
% 3.05/1.48  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_131])).
% 3.05/1.48  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_121])).
% 3.05/1.48  tff(c_203, plain, (![A_119, B_120]: (m1_subset_1(k6_domain_1(u1_struct_0(A_119), B_120), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.05/1.48  tff(c_211, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_203])).
% 3.05/1.48  tff(c_215, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_211])).
% 3.05/1.48  tff(c_216, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_80, c_215])).
% 3.05/1.48  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.48  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.48  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.48  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.48  tff(c_152, plain, (![A_98, D_100, B_99, C_97, E_101]: (k4_enumset1(A_98, A_98, B_99, C_97, D_100, E_101)=k3_enumset1(A_98, B_99, C_97, D_100, E_101))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.48  tff(c_16, plain, (![H_25, C_18, B_17, A_16, D_19, F_21]: (r2_hidden(H_25, k4_enumset1(A_16, B_17, C_18, D_19, H_25, F_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.05/1.48  tff(c_179, plain, (![C_104, B_103, A_105, E_102, D_106]: (r2_hidden(D_106, k3_enumset1(A_105, B_103, C_104, D_106, E_102)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_16])).
% 3.05/1.48  tff(c_190, plain, (![C_109, A_110, B_111, D_112]: (r2_hidden(C_109, k2_enumset1(A_110, B_111, C_109, D_112)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_179])).
% 3.05/1.48  tff(c_194, plain, (![B_113, A_114, C_115]: (r2_hidden(B_113, k1_enumset1(A_114, B_113, C_115)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_190])).
% 3.05/1.48  tff(c_198, plain, (![A_116, B_117]: (r2_hidden(A_116, k2_tarski(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_194])).
% 3.05/1.48  tff(c_201, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_198])).
% 3.05/1.48  tff(c_68, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.05/1.48  tff(c_138, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_68])).
% 3.05/1.48  tff(c_415, plain, (![B_227, A_228, C_229]: (~r2_hidden(B_227, k1_orders_2(A_228, C_229)) | ~r2_hidden(B_227, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(B_227, u1_struct_0(A_228)) | ~l1_orders_2(A_228) | ~v5_orders_2(A_228) | ~v4_orders_2(A_228) | ~v3_orders_2(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.48  tff(c_417, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_138, c_415])).
% 3.05/1.48  tff(c_420, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_216, c_201, c_417])).
% 3.05/1.48  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_420])).
% 3.05/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  Inference rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Ref     : 0
% 3.05/1.48  #Sup     : 70
% 3.05/1.48  #Fact    : 0
% 3.05/1.48  #Define  : 0
% 3.05/1.48  #Split   : 2
% 3.05/1.48  #Chain   : 0
% 3.05/1.48  #Close   : 0
% 3.05/1.48  
% 3.05/1.48  Ordering : KBO
% 3.05/1.48  
% 3.05/1.48  Simplification rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Subsume      : 1
% 3.05/1.48  #Demod        : 24
% 3.05/1.48  #Tautology    : 39
% 3.05/1.48  #SimpNegUnit  : 5
% 3.05/1.48  #BackRed      : 1
% 3.05/1.48  
% 3.05/1.48  #Partial instantiations: 0
% 3.05/1.48  #Strategies tried      : 1
% 3.05/1.48  
% 3.05/1.48  Timing (in seconds)
% 3.05/1.48  ----------------------
% 3.05/1.48  Preprocessing        : 0.36
% 3.05/1.48  Parsing              : 0.19
% 3.05/1.48  CNF conversion       : 0.03
% 3.05/1.48  Main loop            : 0.29
% 3.05/1.48  Inferencing          : 0.10
% 3.05/1.48  Reduction            : 0.08
% 3.05/1.48  Demodulation         : 0.05
% 3.05/1.48  BG Simplification    : 0.02
% 3.05/1.48  Subsumption          : 0.07
% 3.05/1.48  Abstraction          : 0.02
% 3.05/1.48  MUC search           : 0.00
% 3.05/1.48  Cooper               : 0.00
% 3.05/1.48  Total                : 0.68
% 3.05/1.48  Index Insertion      : 0.00
% 3.05/1.48  Index Deletion       : 0.00
% 3.05/1.48  Index Matching       : 0.00
% 3.05/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
