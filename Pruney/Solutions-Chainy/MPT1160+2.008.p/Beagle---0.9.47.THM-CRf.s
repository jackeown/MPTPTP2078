%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 221 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_125,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_78,axiom,(
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

tff(f_108,axiom,(
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

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [A_45] :
      ( k1_struct_0(A_45) = k1_xboole_0
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_46] :
      ( k1_struct_0(A_46) = k1_xboole_0
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_52,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_28,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_53,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1(k3_orders_2(A_69,B_70,C_71),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [A_87,A_88,B_89,C_90] :
      ( m1_subset_1(A_87,u1_struct_0(A_88))
      | ~ r2_hidden(A_87,k3_orders_2(A_88,B_89,C_90))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_119,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_88,B_89,C_90)),u1_struct_0(A_88))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88)
      | k3_orders_2(A_88,B_89,C_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_97,plain,(
    ! [B_76,D_77,A_78,C_79] :
      ( r2_hidden(B_76,D_77)
      | ~ r2_hidden(B_76,k3_orders_2(A_78,D_77,C_79))
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ m1_subset_1(B_76,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_132,plain,(
    ! [A_98,D_99,C_100] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_98,D_99,C_100)),D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_98,D_99,C_100)),u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98)
      | k3_orders_2(A_98,D_99,C_100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_136,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_101,B_102,C_103)),B_102)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101)
      | k3_orders_2(A_101,B_102,C_103) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_119,c_132])).

tff(c_59,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_1,A_50] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_63,plain,(
    ! [A_50] : ~ r2_hidden(A_50,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_156,plain,(
    ! [C_103,A_101] :
      ( ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101)
      | k3_orders_2(A_101,k1_xboole_0,C_103) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_63])).

tff(c_170,plain,(
    ! [C_107,A_108] :
      ( ~ m1_subset_1(C_107,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108)
      | k3_orders_2(A_108,k1_xboole_0,C_107) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_156])).

tff(c_176,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_170])).

tff(c_180,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_176])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_40,c_180])).

tff(c_183,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.30  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.29/1.30  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.29/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.29/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.29/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.29/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.29/1.30  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.29/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.30  
% 2.29/1.32  tff(f_125, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.29/1.32  tff(f_82, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.29/1.32  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.29/1.32  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.29/1.32  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.29/1.32  tff(f_78, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.29/1.32  tff(f_34, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.29/1.32  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.29/1.32  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.29/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.32  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_20, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.32  tff(c_43, plain, (![A_45]: (k1_struct_0(A_45)=k1_xboole_0 | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.29/1.32  tff(c_48, plain, (![A_46]: (k1_struct_0(A_46)=k1_xboole_0 | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.29/1.32  tff(c_52, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.29/1.32  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_53, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.29/1.32  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.29/1.32  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.29/1.32  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.29/1.32  tff(c_85, plain, (![A_69, B_70, C_71]: (m1_subset_1(k3_orders_2(A_69, B_70, C_71), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.29/1.32  tff(c_6, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.29/1.32  tff(c_115, plain, (![A_87, A_88, B_89, C_90]: (m1_subset_1(A_87, u1_struct_0(A_88)) | ~r2_hidden(A_87, k3_orders_2(A_88, B_89, C_90)) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_85, c_6])).
% 2.29/1.32  tff(c_119, plain, (![A_88, B_89, C_90]: (m1_subset_1('#skF_1'(k3_orders_2(A_88, B_89, C_90)), u1_struct_0(A_88)) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88) | k3_orders_2(A_88, B_89, C_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_115])).
% 2.29/1.32  tff(c_97, plain, (![B_76, D_77, A_78, C_79]: (r2_hidden(B_76, D_77) | ~r2_hidden(B_76, k3_orders_2(A_78, D_77, C_79)) | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~m1_subset_1(B_76, u1_struct_0(A_78)) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.32  tff(c_132, plain, (![A_98, D_99, C_100]: (r2_hidden('#skF_1'(k3_orders_2(A_98, D_99, C_100)), D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_98, D_99, C_100)), u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98) | k3_orders_2(A_98, D_99, C_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_97])).
% 2.29/1.32  tff(c_136, plain, (![A_101, B_102, C_103]: (r2_hidden('#skF_1'(k3_orders_2(A_101, B_102, C_103)), B_102) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101) | k3_orders_2(A_101, B_102, C_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_119, c_132])).
% 2.29/1.32  tff(c_59, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.32  tff(c_62, plain, (![A_1, A_50]: (~v1_xboole_0(A_1) | ~r2_hidden(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.29/1.32  tff(c_63, plain, (![A_50]: (~r2_hidden(A_50, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_62])).
% 2.29/1.32  tff(c_156, plain, (![C_103, A_101]: (~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101) | k3_orders_2(A_101, k1_xboole_0, C_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_63])).
% 2.29/1.32  tff(c_170, plain, (![C_107, A_108]: (~m1_subset_1(C_107, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108) | k3_orders_2(A_108, k1_xboole_0, C_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_156])).
% 2.29/1.32  tff(c_176, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_170])).
% 2.29/1.32  tff(c_180, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_176])).
% 2.29/1.32  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_40, c_180])).
% 2.29/1.32  tff(c_183, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_62])).
% 2.29/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.29/1.32  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_2])).
% 2.29/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  Inference rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Ref     : 0
% 2.29/1.32  #Sup     : 30
% 2.29/1.32  #Fact    : 0
% 2.29/1.32  #Define  : 0
% 2.29/1.32  #Split   : 2
% 2.29/1.32  #Chain   : 0
% 2.29/1.32  #Close   : 0
% 2.29/1.32  
% 2.29/1.32  Ordering : KBO
% 2.29/1.32  
% 2.29/1.32  Simplification rules
% 2.29/1.32  ----------------------
% 2.29/1.32  #Subsume      : 5
% 2.29/1.32  #Demod        : 10
% 2.29/1.32  #Tautology    : 3
% 2.29/1.32  #SimpNegUnit  : 3
% 2.29/1.32  #BackRed      : 2
% 2.29/1.32  
% 2.29/1.32  #Partial instantiations: 0
% 2.29/1.32  #Strategies tried      : 1
% 2.29/1.32  
% 2.29/1.32  Timing (in seconds)
% 2.29/1.32  ----------------------
% 2.29/1.32  Preprocessing        : 0.32
% 2.59/1.32  Parsing              : 0.18
% 2.59/1.32  CNF conversion       : 0.02
% 2.59/1.32  Main loop            : 0.25
% 2.59/1.32  Inferencing          : 0.10
% 2.59/1.32  Reduction            : 0.06
% 2.59/1.32  Demodulation         : 0.04
% 2.59/1.32  BG Simplification    : 0.02
% 2.59/1.32  Subsumption          : 0.05
% 2.59/1.32  Abstraction          : 0.01
% 2.59/1.32  MUC search           : 0.00
% 2.59/1.32  Cooper               : 0.00
% 2.59/1.32  Total                : 0.60
% 2.59/1.32  Index Insertion      : 0.00
% 2.59/1.32  Index Deletion       : 0.00
% 2.59/1.32  Index Matching       : 0.00
% 2.59/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
