%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 227 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)
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

tff(f_130,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_83,axiom,(
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

tff(f_113,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41,plain,(
    ! [A_53] :
      ( k1_struct_0(A_53) = k1_xboole_0
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_54] :
      ( k1_struct_0(A_54) = k1_xboole_0
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_50,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_51,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k3_orders_2(A_78,B_79,C_80),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [A_99,A_100,B_101,C_102] :
      ( m1_subset_1(A_99,u1_struct_0(A_100))
      | ~ r2_hidden(A_99,k3_orders_2(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_127,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_100,B_101,C_102)),u1_struct_0(A_100))
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100)
      | k3_orders_2(A_100,B_101,C_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_105,plain,(
    ! [B_88,D_89,A_90,C_91] :
      ( r2_hidden(B_88,D_89)
      | ~ r2_hidden(B_88,k3_orders_2(A_90,D_89,C_91))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(C_91,u1_struct_0(A_90))
      | ~ m1_subset_1(B_88,u1_struct_0(A_90))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_147,plain,(
    ! [A_113,D_114,C_115] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_113,D_114,C_115)),D_114)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_113,D_114,C_115)),u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113)
      | k3_orders_2(A_113,D_114,C_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_151,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_116,B_117,C_118)),B_117)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116)
      | k3_orders_2(A_116,B_117,C_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_127,c_147])).

tff(c_57,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_1,A_58] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_61,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_183,plain,(
    ! [C_118,A_116] :
      ( ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116)
      | k3_orders_2(A_116,k1_xboole_0,C_118) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_151,c_61])).

tff(c_196,plain,(
    ! [C_119,A_120] :
      ( ~ m1_subset_1(C_119,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120)
      | k3_orders_2(A_120,k1_xboole_0,C_119) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_183])).

tff(c_202,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_196])).

tff(c_206,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_202])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_38,c_206])).

tff(c_209,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  %$ r2_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.34/1.30  
% 2.34/1.30  %Foreground sorts:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Background operators:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Foreground operators:
% 2.34/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.30  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.34/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.34/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.34/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.34/1.30  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.34/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.30  
% 2.34/1.32  tff(f_130, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.34/1.32  tff(f_87, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.34/1.32  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.34/1.32  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.34/1.32  tff(f_62, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.34/1.32  tff(f_83, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.34/1.32  tff(f_34, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.34/1.32  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.34/1.32  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.34/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.34/1.32  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_18, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.32  tff(c_41, plain, (![A_53]: (k1_struct_0(A_53)=k1_xboole_0 | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.32  tff(c_46, plain, (![A_54]: (k1_struct_0(A_54)=k1_xboole_0 | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.34/1.32  tff(c_50, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.34/1.32  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_51, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 2.34/1.32  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.34/1.32  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.34/1.32  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.32  tff(c_88, plain, (![A_78, B_79, C_80]: (m1_subset_1(k3_orders_2(A_78, B_79, C_80), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.34/1.32  tff(c_6, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.34/1.32  tff(c_123, plain, (![A_99, A_100, B_101, C_102]: (m1_subset_1(A_99, u1_struct_0(A_100)) | ~r2_hidden(A_99, k3_orders_2(A_100, B_101, C_102)) | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_88, c_6])).
% 2.34/1.32  tff(c_127, plain, (![A_100, B_101, C_102]: (m1_subset_1('#skF_1'(k3_orders_2(A_100, B_101, C_102)), u1_struct_0(A_100)) | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100) | k3_orders_2(A_100, B_101, C_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_123])).
% 2.34/1.32  tff(c_105, plain, (![B_88, D_89, A_90, C_91]: (r2_hidden(B_88, D_89) | ~r2_hidden(B_88, k3_orders_2(A_90, D_89, C_91)) | ~m1_subset_1(D_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(C_91, u1_struct_0(A_90)) | ~m1_subset_1(B_88, u1_struct_0(A_90)) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.34/1.32  tff(c_147, plain, (![A_113, D_114, C_115]: (r2_hidden('#skF_1'(k3_orders_2(A_113, D_114, C_115)), D_114) | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_113, D_114, C_115)), u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113) | k3_orders_2(A_113, D_114, C_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.34/1.32  tff(c_151, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_1'(k3_orders_2(A_116, B_117, C_118)), B_117) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116) | k3_orders_2(A_116, B_117, C_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_127, c_147])).
% 2.34/1.32  tff(c_57, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.32  tff(c_60, plain, (![A_1, A_58]: (~v1_xboole_0(A_1) | ~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.34/1.32  tff(c_61, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 2.34/1.32  tff(c_183, plain, (![C_118, A_116]: (~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116) | k3_orders_2(A_116, k1_xboole_0, C_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_151, c_61])).
% 2.34/1.32  tff(c_196, plain, (![C_119, A_120]: (~m1_subset_1(C_119, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120) | k3_orders_2(A_120, k1_xboole_0, C_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_183])).
% 2.34/1.32  tff(c_202, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_196])).
% 2.34/1.32  tff(c_206, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_202])).
% 2.34/1.32  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_38, c_206])).
% 2.34/1.32  tff(c_209, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_60])).
% 2.34/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.34/1.32  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_2])).
% 2.34/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  Inference rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Ref     : 0
% 2.34/1.32  #Sup     : 35
% 2.34/1.32  #Fact    : 0
% 2.34/1.32  #Define  : 0
% 2.34/1.32  #Split   : 2
% 2.34/1.32  #Chain   : 0
% 2.34/1.32  #Close   : 0
% 2.34/1.32  
% 2.34/1.32  Ordering : KBO
% 2.34/1.32  
% 2.34/1.32  Simplification rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Subsume      : 5
% 2.34/1.32  #Demod        : 10
% 2.34/1.32  #Tautology    : 3
% 2.34/1.32  #SimpNegUnit  : 3
% 2.34/1.32  #BackRed      : 2
% 2.34/1.32  
% 2.34/1.32  #Partial instantiations: 0
% 2.34/1.32  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.32  Preprocessing        : 0.31
% 2.34/1.32  Parsing              : 0.18
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.25
% 2.34/1.32  Inferencing          : 0.10
% 2.34/1.32  Reduction            : 0.06
% 2.34/1.32  Demodulation         : 0.04
% 2.34/1.32  BG Simplification    : 0.01
% 2.34/1.32  Subsumption          : 0.05
% 2.34/1.32  Abstraction          : 0.01
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.59
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
