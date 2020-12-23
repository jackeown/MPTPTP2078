%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 221 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_41,plain,(
    ! [A_41] :
      ( k1_struct_0(A_41) = k1_xboole_0
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_42] :
      ( k1_struct_0(A_42) = k1_xboole_0
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_50,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_51,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k3_orders_2(A_57,B_58,C_59),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(C_59,u1_struct_0(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_71,A_72,B_73,C_74] :
      ( m1_subset_1(A_71,u1_struct_0(A_72))
      | ~ r2_hidden(A_71,k3_orders_2(A_72,B_73,C_74))
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_114,plain,(
    ! [A_72,B_73,C_74] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_72,B_73,C_74)),u1_struct_0(A_72))
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72)
      | k3_orders_2(A_72,B_73,C_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_104,plain,(
    ! [B_67,D_68,A_69,C_70] :
      ( r2_hidden(B_67,D_68)
      | ~ r2_hidden(B_67,k3_orders_2(A_69,D_68,C_70))
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(C_70,u1_struct_0(A_69))
      | ~ m1_subset_1(B_67,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_132,plain,(
    ! [A_86,D_87,C_88] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_86,D_87,C_88)),D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_86,D_87,C_88)),u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86)
      | k3_orders_2(A_86,D_87,C_88) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_136,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_89,B_90,C_91)),B_90)
      | ~ m1_subset_1(C_91,u1_struct_0(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89)
      | k3_orders_2(A_89,B_90,C_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_132])).

tff(c_57,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_1,A_46] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_61,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_159,plain,(
    ! [C_91,A_89] :
      ( ~ m1_subset_1(C_91,u1_struct_0(A_89))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89)
      | k3_orders_2(A_89,k1_xboole_0,C_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_61])).

tff(c_169,plain,(
    ! [C_92,A_93] :
      ( ~ m1_subset_1(C_92,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93)
      | k3_orders_2(A_93,k1_xboole_0,C_92) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_159])).

tff(c_175,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_169])).

tff(c_179,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_175])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_38,c_179])).

tff(c_182,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  %$ r2_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.45/1.37  
% 2.45/1.37  %Foreground sorts:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Background operators:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Foreground operators:
% 2.45/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.37  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.45/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.45/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.45/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.45/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.37  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.45/1.37  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.45/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.37  
% 2.58/1.38  tff(f_124, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.58/1.38  tff(f_81, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.58/1.38  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.58/1.38  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.58/1.38  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_mcart_1)).
% 2.58/1.38  tff(f_77, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.58/1.38  tff(f_34, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.58/1.38  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.58/1.38  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.58/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.38  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_18, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.38  tff(c_41, plain, (![A_41]: (k1_struct_0(A_41)=k1_xboole_0 | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.38  tff(c_46, plain, (![A_42]: (k1_struct_0(A_42)=k1_xboole_0 | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.58/1.38  tff(c_50, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.58/1.38  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_51, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 2.58/1.38  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.58/1.38  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.58/1.38  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.38  tff(c_85, plain, (![A_57, B_58, C_59]: (m1_subset_1(k3_orders_2(A_57, B_58, C_59), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(C_59, u1_struct_0(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.58/1.38  tff(c_6, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.58/1.38  tff(c_110, plain, (![A_71, A_72, B_73, C_74]: (m1_subset_1(A_71, u1_struct_0(A_72)) | ~r2_hidden(A_71, k3_orders_2(A_72, B_73, C_74)) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_85, c_6])).
% 2.58/1.38  tff(c_114, plain, (![A_72, B_73, C_74]: (m1_subset_1('#skF_1'(k3_orders_2(A_72, B_73, C_74)), u1_struct_0(A_72)) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72) | k3_orders_2(A_72, B_73, C_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_110])).
% 2.58/1.38  tff(c_104, plain, (![B_67, D_68, A_69, C_70]: (r2_hidden(B_67, D_68) | ~r2_hidden(B_67, k3_orders_2(A_69, D_68, C_70)) | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(C_70, u1_struct_0(A_69)) | ~m1_subset_1(B_67, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.58/1.38  tff(c_132, plain, (![A_86, D_87, C_88]: (r2_hidden('#skF_1'(k3_orders_2(A_86, D_87, C_88)), D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_86, D_87, C_88)), u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86) | k3_orders_2(A_86, D_87, C_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_104])).
% 2.58/1.38  tff(c_136, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_1'(k3_orders_2(A_89, B_90, C_91)), B_90) | ~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89) | k3_orders_2(A_89, B_90, C_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_132])).
% 2.58/1.38  tff(c_57, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.38  tff(c_60, plain, (![A_1, A_46]: (~v1_xboole_0(A_1) | ~r2_hidden(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.58/1.38  tff(c_61, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 2.58/1.38  tff(c_159, plain, (![C_91, A_89]: (~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89) | k3_orders_2(A_89, k1_xboole_0, C_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_61])).
% 2.58/1.38  tff(c_169, plain, (![C_92, A_93]: (~m1_subset_1(C_92, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93) | k3_orders_2(A_93, k1_xboole_0, C_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_159])).
% 2.58/1.38  tff(c_175, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_169])).
% 2.58/1.38  tff(c_179, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_175])).
% 2.58/1.38  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_38, c_179])).
% 2.58/1.38  tff(c_182, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_60])).
% 2.58/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.38  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_2])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 30
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 2
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Subsume      : 5
% 2.58/1.38  #Demod        : 10
% 2.58/1.38  #Tautology    : 3
% 2.58/1.38  #SimpNegUnit  : 3
% 2.58/1.38  #BackRed      : 2
% 2.58/1.38  
% 2.58/1.38  #Partial instantiations: 0
% 2.58/1.38  #Strategies tried      : 1
% 2.58/1.38  
% 2.58/1.38  Timing (in seconds)
% 2.58/1.38  ----------------------
% 2.58/1.38  Preprocessing        : 0.31
% 2.58/1.38  Parsing              : 0.18
% 2.58/1.38  CNF conversion       : 0.02
% 2.58/1.38  Main loop            : 0.23
% 2.58/1.38  Inferencing          : 0.09
% 2.58/1.39  Reduction            : 0.05
% 2.58/1.39  Demodulation         : 0.04
% 2.58/1.39  BG Simplification    : 0.01
% 2.58/1.39  Subsumption          : 0.05
% 2.58/1.39  Abstraction          : 0.01
% 2.58/1.39  MUC search           : 0.00
% 2.58/1.39  Cooper               : 0.00
% 2.58/1.39  Total                : 0.57
% 2.58/1.39  Index Insertion      : 0.00
% 2.58/1.39  Index Deletion       : 0.00
% 2.58/1.39  Index Matching       : 0.00
% 2.58/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
