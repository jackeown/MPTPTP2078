%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 197 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_101,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_73,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = k1_xboole_0
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_41] :
      ( k1_struct_0(A_41) = k1_xboole_0
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_89,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_28,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_90,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_28])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k3_orders_2(A_47,B_48,C_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_orders_2(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v4_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [A_50,A_51,B_52,C_53] :
      ( m1_subset_1(A_50,u1_struct_0(A_51))
      | ~ r2_hidden(A_50,k3_orders_2(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_orders_2(A_51)
      | ~ v5_orders_2(A_51)
      | ~ v4_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_110,c_14])).

tff(c_118,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_51,B_52,C_53)),u1_struct_0(A_51))
      | ~ m1_subset_1(C_53,u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_orders_2(A_51)
      | ~ v5_orders_2(A_51)
      | ~ v4_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | v2_struct_0(A_51)
      | k3_orders_2(A_51,B_52,C_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_119,plain,(
    ! [B_54,D_55,A_56,C_57] :
      ( r2_hidden(B_54,D_55)
      | ~ r2_hidden(B_54,k3_orders_2(A_56,D_55,C_57))
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ m1_subset_1(B_54,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_138,plain,(
    ! [A_69,D_70,C_71] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_69,D_70,C_71)),D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_69,D_70,C_71)),u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69)
      | k3_orders_2(A_69,D_70,C_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_142,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_72,B_73,C_74)),B_73)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72)
      | k3_orders_2(A_72,B_73,C_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_118,c_138])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_155,plain,(
    ! [C_74,A_72] :
      ( ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72)
      | k3_orders_2(A_72,k1_xboole_0,C_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_142,c_68])).

tff(c_166,plain,(
    ! [C_78,A_79] :
      ( ~ m1_subset_1(C_78,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79)
      | k3_orders_2(A_79,k1_xboole_0,C_78) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_155])).

tff(c_172,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_176,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_172])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_40,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.27  
% 2.32/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.27  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.32/1.27  
% 2.32/1.27  %Foreground sorts:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Background operators:
% 2.32/1.27  
% 2.32/1.27  
% 2.32/1.27  %Foreground operators:
% 2.32/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.27  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.32/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.32/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.32/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.27  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.32/1.27  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.32/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.27  
% 2.32/1.29  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.32/1.29  tff(f_75, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.32/1.29  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.32/1.29  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.32/1.29  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.32/1.29  tff(f_71, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.32/1.29  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.32/1.29  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.32/1.29  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.32/1.29  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.32/1.29  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.32/1.29  tff(c_73, plain, (![A_39]: (k1_struct_0(A_39)=k1_xboole_0 | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.29  tff(c_85, plain, (![A_41]: (k1_struct_0(A_41)=k1_xboole_0 | ~l1_orders_2(A_41))), inference(resolution, [status(thm)], [c_20, c_73])).
% 2.32/1.29  tff(c_89, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_85])).
% 2.32/1.29  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_90, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_28])).
% 2.32/1.29  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.32/1.29  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.29  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.32/1.29  tff(c_110, plain, (![A_47, B_48, C_49]: (m1_subset_1(k3_orders_2(A_47, B_48, C_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_orders_2(A_47) | ~v5_orders_2(A_47) | ~v4_orders_2(A_47) | ~v3_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.29  tff(c_14, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.29  tff(c_114, plain, (![A_50, A_51, B_52, C_53]: (m1_subset_1(A_50, u1_struct_0(A_51)) | ~r2_hidden(A_50, k3_orders_2(A_51, B_52, C_53)) | ~m1_subset_1(C_53, u1_struct_0(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_orders_2(A_51) | ~v5_orders_2(A_51) | ~v4_orders_2(A_51) | ~v3_orders_2(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_110, c_14])).
% 2.32/1.29  tff(c_118, plain, (![A_51, B_52, C_53]: (m1_subset_1('#skF_1'(k3_orders_2(A_51, B_52, C_53)), u1_struct_0(A_51)) | ~m1_subset_1(C_53, u1_struct_0(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_orders_2(A_51) | ~v5_orders_2(A_51) | ~v4_orders_2(A_51) | ~v3_orders_2(A_51) | v2_struct_0(A_51) | k3_orders_2(A_51, B_52, C_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_114])).
% 2.32/1.29  tff(c_119, plain, (![B_54, D_55, A_56, C_57]: (r2_hidden(B_54, D_55) | ~r2_hidden(B_54, k3_orders_2(A_56, D_55, C_57)) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~m1_subset_1(B_54, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.32/1.29  tff(c_138, plain, (![A_69, D_70, C_71]: (r2_hidden('#skF_1'(k3_orders_2(A_69, D_70, C_71)), D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_69, D_70, C_71)), u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69) | k3_orders_2(A_69, D_70, C_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_119])).
% 2.32/1.29  tff(c_142, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_1'(k3_orders_2(A_72, B_73, C_74)), B_73) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72) | k3_orders_2(A_72, B_73, C_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_118, c_138])).
% 2.32/1.29  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.32/1.29  tff(c_65, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.32/1.29  tff(c_68, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 2.32/1.29  tff(c_155, plain, (![C_74, A_72]: (~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72) | k3_orders_2(A_72, k1_xboole_0, C_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_142, c_68])).
% 2.32/1.29  tff(c_166, plain, (![C_78, A_79]: (~m1_subset_1(C_78, u1_struct_0(A_79)) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79) | k3_orders_2(A_79, k1_xboole_0, C_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_155])).
% 2.32/1.29  tff(c_172, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_166])).
% 2.32/1.29  tff(c_176, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_172])).
% 2.32/1.29  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_40, c_176])).
% 2.32/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.29  
% 2.32/1.29  Inference rules
% 2.32/1.29  ----------------------
% 2.32/1.29  #Ref     : 0
% 2.32/1.29  #Sup     : 30
% 2.32/1.29  #Fact    : 0
% 2.32/1.29  #Define  : 0
% 2.32/1.29  #Split   : 0
% 2.32/1.29  #Chain   : 0
% 2.32/1.29  #Close   : 0
% 2.32/1.29  
% 2.32/1.29  Ordering : KBO
% 2.32/1.29  
% 2.32/1.29  Simplification rules
% 2.32/1.29  ----------------------
% 2.32/1.29  #Subsume      : 4
% 2.32/1.29  #Demod        : 6
% 2.32/1.29  #Tautology    : 11
% 2.32/1.29  #SimpNegUnit  : 1
% 2.32/1.29  #BackRed      : 1
% 2.32/1.29  
% 2.32/1.29  #Partial instantiations: 0
% 2.32/1.29  #Strategies tried      : 1
% 2.32/1.29  
% 2.32/1.29  Timing (in seconds)
% 2.32/1.29  ----------------------
% 2.32/1.29  Preprocessing        : 0.30
% 2.32/1.29  Parsing              : 0.17
% 2.32/1.29  CNF conversion       : 0.02
% 2.32/1.29  Main loop            : 0.21
% 2.32/1.29  Inferencing          : 0.09
% 2.32/1.29  Reduction            : 0.05
% 2.32/1.29  Demodulation         : 0.04
% 2.32/1.29  BG Simplification    : 0.01
% 2.32/1.29  Subsumption          : 0.04
% 2.32/1.29  Abstraction          : 0.01
% 2.32/1.29  MUC search           : 0.00
% 2.32/1.29  Cooper               : 0.00
% 2.32/1.29  Total                : 0.55
% 2.32/1.29  Index Insertion      : 0.00
% 2.32/1.29  Index Deletion       : 0.00
% 2.32/1.29  Index Matching       : 0.00
% 2.32/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
