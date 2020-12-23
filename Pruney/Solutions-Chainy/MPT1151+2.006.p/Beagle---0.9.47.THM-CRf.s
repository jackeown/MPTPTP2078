%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 118 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 343 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_50,B_51] :
      ( k2_orders_2(A_50,B_51) = a_2_1_orders_2(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50)
      | ~ v3_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [A_52] :
      ( k2_orders_2(A_52,k1_xboole_0) = a_2_1_orders_2(A_52,k1_xboole_0)
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_90,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_93,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_90])).

tff(c_94,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_93])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_orders_2(A_35) ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_57,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_34,plain,(
    k2_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_34])).

tff(c_95,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_58])).

tff(c_100,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k2_orders_2(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53)
      | ~ v4_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_100])).

tff(c_112,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_8,c_108])).

tff(c_113,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_112])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1('#skF_1'(A_2,B_3),A_2)
      | B_3 = A_2
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_311,plain,(
    ! [D_72,B_73,C_74] :
      ( r2_hidden('#skF_3'(D_72,B_73,C_74,D_72),C_74)
      | r2_hidden(D_72,a_2_1_orders_2(B_73,C_74))
      | ~ m1_subset_1(D_72,u1_struct_0(B_73))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(B_73)))
      | ~ l1_orders_2(B_73)
      | ~ v5_orders_2(B_73)
      | ~ v4_orders_2(B_73)
      | ~ v3_orders_2(B_73)
      | v2_struct_0(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_427,plain,(
    ! [D_80,B_81] :
      ( r2_hidden('#skF_3'(D_80,B_81,k1_xboole_0,D_80),k1_xboole_0)
      | r2_hidden(D_80,a_2_1_orders_2(B_81,k1_xboole_0))
      | ~ m1_subset_1(D_80,u1_struct_0(B_81))
      | ~ l1_orders_2(B_81)
      | ~ v5_orders_2(B_81)
      | ~ v4_orders_2(B_81)
      | ~ v3_orders_2(B_81)
      | v2_struct_0(B_81) ) ),
    inference(resolution,[status(thm)],[c_8,c_311])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_432,plain,(
    ! [D_80,B_81] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(D_80,B_81,k1_xboole_0,D_80))
      | r2_hidden(D_80,a_2_1_orders_2(B_81,k1_xboole_0))
      | ~ m1_subset_1(D_80,u1_struct_0(B_81))
      | ~ l1_orders_2(B_81)
      | ~ v5_orders_2(B_81)
      | ~ v4_orders_2(B_81)
      | ~ v3_orders_2(B_81)
      | v2_struct_0(B_81) ) ),
    inference(resolution,[status(thm)],[c_427,c_12])).

tff(c_437,plain,(
    ! [D_82,B_83] :
      ( r2_hidden(D_82,a_2_1_orders_2(B_83,k1_xboole_0))
      | ~ m1_subset_1(D_82,u1_struct_0(B_83))
      | ~ l1_orders_2(B_83)
      | ~ v5_orders_2(B_83)
      | ~ v4_orders_2(B_83)
      | ~ v3_orders_2(B_83)
      | v2_struct_0(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_432])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( ~ r2_hidden('#skF_1'(A_2,B_3),B_3)
      | B_3 = A_2
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_479,plain,(
    ! [B_91,A_92] :
      ( a_2_1_orders_2(B_91,k1_xboole_0) = A_92
      | ~ m1_subset_1(a_2_1_orders_2(B_91,k1_xboole_0),k1_zfmisc_1(A_92))
      | ~ m1_subset_1('#skF_1'(A_92,a_2_1_orders_2(B_91,k1_xboole_0)),u1_struct_0(B_91))
      | ~ l1_orders_2(B_91)
      | ~ v5_orders_2(B_91)
      | ~ v4_orders_2(B_91)
      | ~ v3_orders_2(B_91)
      | v2_struct_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_437,c_4])).

tff(c_485,plain,(
    ! [B_93] :
      ( ~ l1_orders_2(B_93)
      | ~ v5_orders_2(B_93)
      | ~ v4_orders_2(B_93)
      | ~ v3_orders_2(B_93)
      | v2_struct_0(B_93)
      | a_2_1_orders_2(B_93,k1_xboole_0) = u1_struct_0(B_93)
      | ~ m1_subset_1(a_2_1_orders_2(B_93,k1_xboole_0),k1_zfmisc_1(u1_struct_0(B_93))) ) ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_488,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_485])).

tff(c_491,plain,
    ( v2_struct_0('#skF_4')
    | a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_488])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_44,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.35  
% 2.72/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.36  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.72/1.36  
% 2.72/1.36  %Foreground sorts:
% 2.72/1.36  
% 2.72/1.36  
% 2.72/1.36  %Background operators:
% 2.72/1.36  
% 2.72/1.36  
% 2.72/1.36  %Foreground operators:
% 2.72/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.72/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.36  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 2.72/1.36  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.72/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.72/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.72/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.72/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.72/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.36  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.72/1.36  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.72/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.72/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.72/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.36  
% 2.72/1.37  tff(f_129, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_orders_2)).
% 2.72/1.37  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.72/1.37  tff(f_69, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 2.72/1.37  tff(f_88, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.72/1.37  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.72/1.37  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 2.72/1.37  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 2.72/1.37  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.37  tff(f_115, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 2.72/1.37  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.72/1.37  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_42, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_40, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_36, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_38, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_8, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.37  tff(c_76, plain, (![A_50, B_51]: (k2_orders_2(A_50, B_51)=a_2_1_orders_2(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50) | ~v3_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.72/1.37  tff(c_87, plain, (![A_52]: (k2_orders_2(A_52, k1_xboole_0)=a_2_1_orders_2(A_52, k1_xboole_0) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.72/1.37  tff(c_90, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.72/1.37  tff(c_93, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_90])).
% 2.72/1.37  tff(c_94, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_93])).
% 2.72/1.37  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.72/1.37  tff(c_48, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.37  tff(c_53, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_orders_2(A_35))), inference(resolution, [status(thm)], [c_20, c_48])).
% 2.72/1.37  tff(c_57, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.72/1.37  tff(c_34, plain, (k2_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.72/1.37  tff(c_58, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_34])).
% 2.72/1.37  tff(c_95, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_58])).
% 2.72/1.37  tff(c_100, plain, (![A_53, B_54]: (m1_subset_1(k2_orders_2(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.37  tff(c_108, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_94, c_100])).
% 2.72/1.37  tff(c_112, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_8, c_108])).
% 2.72/1.37  tff(c_113, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_112])).
% 2.72/1.37  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1('#skF_1'(A_2, B_3), A_2) | B_3=A_2 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.72/1.37  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.37  tff(c_311, plain, (![D_72, B_73, C_74]: (r2_hidden('#skF_3'(D_72, B_73, C_74, D_72), C_74) | r2_hidden(D_72, a_2_1_orders_2(B_73, C_74)) | ~m1_subset_1(D_72, u1_struct_0(B_73)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(B_73))) | ~l1_orders_2(B_73) | ~v5_orders_2(B_73) | ~v4_orders_2(B_73) | ~v3_orders_2(B_73) | v2_struct_0(B_73))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.37  tff(c_427, plain, (![D_80, B_81]: (r2_hidden('#skF_3'(D_80, B_81, k1_xboole_0, D_80), k1_xboole_0) | r2_hidden(D_80, a_2_1_orders_2(B_81, k1_xboole_0)) | ~m1_subset_1(D_80, u1_struct_0(B_81)) | ~l1_orders_2(B_81) | ~v5_orders_2(B_81) | ~v4_orders_2(B_81) | ~v3_orders_2(B_81) | v2_struct_0(B_81))), inference(resolution, [status(thm)], [c_8, c_311])).
% 2.72/1.37  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.37  tff(c_432, plain, (![D_80, B_81]: (~r1_tarski(k1_xboole_0, '#skF_3'(D_80, B_81, k1_xboole_0, D_80)) | r2_hidden(D_80, a_2_1_orders_2(B_81, k1_xboole_0)) | ~m1_subset_1(D_80, u1_struct_0(B_81)) | ~l1_orders_2(B_81) | ~v5_orders_2(B_81) | ~v4_orders_2(B_81) | ~v3_orders_2(B_81) | v2_struct_0(B_81))), inference(resolution, [status(thm)], [c_427, c_12])).
% 2.72/1.37  tff(c_437, plain, (![D_82, B_83]: (r2_hidden(D_82, a_2_1_orders_2(B_83, k1_xboole_0)) | ~m1_subset_1(D_82, u1_struct_0(B_83)) | ~l1_orders_2(B_83) | ~v5_orders_2(B_83) | ~v4_orders_2(B_83) | ~v3_orders_2(B_83) | v2_struct_0(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_432])).
% 2.72/1.37  tff(c_4, plain, (![A_2, B_3]: (~r2_hidden('#skF_1'(A_2, B_3), B_3) | B_3=A_2 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.72/1.37  tff(c_479, plain, (![B_91, A_92]: (a_2_1_orders_2(B_91, k1_xboole_0)=A_92 | ~m1_subset_1(a_2_1_orders_2(B_91, k1_xboole_0), k1_zfmisc_1(A_92)) | ~m1_subset_1('#skF_1'(A_92, a_2_1_orders_2(B_91, k1_xboole_0)), u1_struct_0(B_91)) | ~l1_orders_2(B_91) | ~v5_orders_2(B_91) | ~v4_orders_2(B_91) | ~v3_orders_2(B_91) | v2_struct_0(B_91))), inference(resolution, [status(thm)], [c_437, c_4])).
% 2.72/1.37  tff(c_485, plain, (![B_93]: (~l1_orders_2(B_93) | ~v5_orders_2(B_93) | ~v4_orders_2(B_93) | ~v3_orders_2(B_93) | v2_struct_0(B_93) | a_2_1_orders_2(B_93, k1_xboole_0)=u1_struct_0(B_93) | ~m1_subset_1(a_2_1_orders_2(B_93, k1_xboole_0), k1_zfmisc_1(u1_struct_0(B_93))))), inference(resolution, [status(thm)], [c_6, c_479])).
% 2.72/1.37  tff(c_488, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_113, c_485])).
% 2.72/1.37  tff(c_491, plain, (v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_488])).
% 2.72/1.37  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_44, c_491])).
% 2.72/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  Inference rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Ref     : 0
% 2.72/1.37  #Sup     : 90
% 2.72/1.37  #Fact    : 0
% 2.72/1.37  #Define  : 0
% 2.72/1.37  #Split   : 0
% 2.72/1.37  #Chain   : 0
% 2.72/1.37  #Close   : 0
% 2.72/1.37  
% 2.72/1.37  Ordering : KBO
% 2.72/1.37  
% 2.72/1.37  Simplification rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Subsume      : 10
% 2.72/1.37  #Demod        : 186
% 2.72/1.37  #Tautology    : 25
% 2.72/1.37  #SimpNegUnit  : 38
% 2.72/1.37  #BackRed      : 2
% 2.72/1.37  
% 2.72/1.37  #Partial instantiations: 0
% 2.72/1.37  #Strategies tried      : 1
% 2.72/1.37  
% 2.72/1.37  Timing (in seconds)
% 2.72/1.37  ----------------------
% 2.72/1.37  Preprocessing        : 0.32
% 2.72/1.37  Parsing              : 0.17
% 2.72/1.37  CNF conversion       : 0.02
% 2.72/1.37  Main loop            : 0.30
% 2.72/1.37  Inferencing          : 0.11
% 2.72/1.37  Reduction            : 0.09
% 2.72/1.37  Demodulation         : 0.07
% 2.72/1.37  BG Simplification    : 0.02
% 2.72/1.37  Subsumption          : 0.06
% 2.72/1.37  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.65
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
