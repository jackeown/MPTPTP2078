%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 354 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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
       => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_116,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_52,B_53] :
      ( k2_orders_2(A_52,B_53) = a_2_1_orders_2(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    ! [A_54] :
      ( k2_orders_2(A_54,k1_xboole_0) = a_2_1_orders_2(A_54,k1_xboole_0)
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_98,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_101,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_98])).

tff(c_102,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) = a_2_1_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_101])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47,plain,(
    ! [A_33] :
      ( k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_56,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_52])).

tff(c_34,plain,(
    k2_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_57,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34])).

tff(c_103,plain,(
    a_2_1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_57])).

tff(c_108,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k2_orders_2(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_118,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_108])).

tff(c_123,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_8,c_118])).

tff(c_124,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_123])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [C_35,B_36,A_37] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_4,A_37] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_66,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_443,plain,(
    ! [D_80,B_81,C_82] :
      ( r2_hidden('#skF_3'(D_80,B_81,C_82,D_80),C_82)
      | r2_hidden(D_80,a_2_1_orders_2(B_81,C_82))
      | ~ m1_subset_1(D_80,u1_struct_0(B_81))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(B_81)))
      | ~ l1_orders_2(B_81)
      | ~ v5_orders_2(B_81)
      | ~ v4_orders_2(B_81)
      | ~ v3_orders_2(B_81)
      | v2_struct_0(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_463,plain,(
    ! [D_80,B_81] :
      ( r2_hidden('#skF_3'(D_80,B_81,k1_xboole_0,D_80),k1_xboole_0)
      | r2_hidden(D_80,a_2_1_orders_2(B_81,k1_xboole_0))
      | ~ m1_subset_1(D_80,u1_struct_0(B_81))
      | ~ l1_orders_2(B_81)
      | ~ v5_orders_2(B_81)
      | ~ v4_orders_2(B_81)
      | ~ v3_orders_2(B_81)
      | v2_struct_0(B_81) ) ),
    inference(resolution,[status(thm)],[c_8,c_443])).

tff(c_493,plain,(
    ! [D_83,B_84] :
      ( r2_hidden(D_83,a_2_1_orders_2(B_84,k1_xboole_0))
      | ~ m1_subset_1(D_83,u1_struct_0(B_84))
      | ~ l1_orders_2(B_84)
      | ~ v5_orders_2(B_84)
      | ~ v4_orders_2(B_84)
      | ~ v3_orders_2(B_84)
      | v2_struct_0(B_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_463])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_593,plain,(
    ! [B_91,A_92] :
      ( a_2_1_orders_2(B_91,k1_xboole_0) = A_92
      | ~ m1_subset_1(a_2_1_orders_2(B_91,k1_xboole_0),k1_zfmisc_1(A_92))
      | ~ m1_subset_1('#skF_1'(A_92,a_2_1_orders_2(B_91,k1_xboole_0)),u1_struct_0(B_91))
      | ~ l1_orders_2(B_91)
      | ~ v5_orders_2(B_91)
      | ~ v4_orders_2(B_91)
      | ~ v3_orders_2(B_91)
      | v2_struct_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_493,c_4])).

tff(c_599,plain,(
    ! [B_93] :
      ( ~ l1_orders_2(B_93)
      | ~ v5_orders_2(B_93)
      | ~ v4_orders_2(B_93)
      | ~ v3_orders_2(B_93)
      | v2_struct_0(B_93)
      | a_2_1_orders_2(B_93,k1_xboole_0) = u1_struct_0(B_93)
      | ~ m1_subset_1(a_2_1_orders_2(B_93,k1_xboole_0),k1_zfmisc_1(u1_struct_0(B_93))) ) ),
    inference(resolution,[status(thm)],[c_6,c_593])).

tff(c_602,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_599])).

tff(c_605,plain,
    ( v2_struct_0('#skF_4')
    | a_2_1_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_602])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_44,c_605])).

tff(c_608,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.77  
% 3.64/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.78  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.64/1.78  
% 3.64/1.78  %Foreground sorts:
% 3.64/1.78  
% 3.64/1.78  
% 3.64/1.78  %Background operators:
% 3.64/1.78  
% 3.64/1.78  
% 3.64/1.78  %Foreground operators:
% 3.64/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.78  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.64/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.78  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.64/1.78  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.64/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.64/1.78  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.64/1.78  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.64/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.64/1.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.64/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.78  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.78  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.64/1.78  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.64/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.64/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.78  
% 3.64/1.80  tff(f_130, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_orders_2)).
% 3.64/1.80  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.64/1.80  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.64/1.80  tff(f_89, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.64/1.80  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 3.64/1.80  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 3.64/1.80  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.64/1.80  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.64/1.80  tff(f_116, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.64/1.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.64/1.80  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_42, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_40, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_36, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_38, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.80  tff(c_84, plain, (![A_52, B_53]: (k2_orders_2(A_52, B_53)=a_2_1_orders_2(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.80  tff(c_95, plain, (![A_54]: (k2_orders_2(A_54, k1_xboole_0)=a_2_1_orders_2(A_54, k1_xboole_0) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_8, c_84])).
% 3.64/1.80  tff(c_98, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_95])).
% 3.64/1.80  tff(c_101, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_98])).
% 3.64/1.80  tff(c_102, plain, (k2_orders_2('#skF_4', k1_xboole_0)=a_2_1_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_101])).
% 3.64/1.80  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.64/1.80  tff(c_47, plain, (![A_33]: (k1_struct_0(A_33)=k1_xboole_0 | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.64/1.80  tff(c_52, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_20, c_47])).
% 3.64/1.80  tff(c_56, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_52])).
% 3.64/1.80  tff(c_34, plain, (k2_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.64/1.80  tff(c_57, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34])).
% 3.64/1.80  tff(c_103, plain, (a_2_1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_57])).
% 3.64/1.80  tff(c_108, plain, (![A_55, B_56]: (m1_subset_1(k2_orders_2(A_55, B_56), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.64/1.80  tff(c_118, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_102, c_108])).
% 3.64/1.80  tff(c_123, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_8, c_118])).
% 3.64/1.80  tff(c_124, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_123])).
% 3.64/1.80  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.80  tff(c_62, plain, (![C_35, B_36, A_37]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.80  tff(c_65, plain, (![A_4, A_37]: (~v1_xboole_0(A_4) | ~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_62])).
% 3.64/1.80  tff(c_66, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_65])).
% 3.64/1.80  tff(c_443, plain, (![D_80, B_81, C_82]: (r2_hidden('#skF_3'(D_80, B_81, C_82, D_80), C_82) | r2_hidden(D_80, a_2_1_orders_2(B_81, C_82)) | ~m1_subset_1(D_80, u1_struct_0(B_81)) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(B_81))) | ~l1_orders_2(B_81) | ~v5_orders_2(B_81) | ~v4_orders_2(B_81) | ~v3_orders_2(B_81) | v2_struct_0(B_81))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.64/1.80  tff(c_463, plain, (![D_80, B_81]: (r2_hidden('#skF_3'(D_80, B_81, k1_xboole_0, D_80), k1_xboole_0) | r2_hidden(D_80, a_2_1_orders_2(B_81, k1_xboole_0)) | ~m1_subset_1(D_80, u1_struct_0(B_81)) | ~l1_orders_2(B_81) | ~v5_orders_2(B_81) | ~v4_orders_2(B_81) | ~v3_orders_2(B_81) | v2_struct_0(B_81))), inference(resolution, [status(thm)], [c_8, c_443])).
% 3.64/1.80  tff(c_493, plain, (![D_83, B_84]: (r2_hidden(D_83, a_2_1_orders_2(B_84, k1_xboole_0)) | ~m1_subset_1(D_83, u1_struct_0(B_84)) | ~l1_orders_2(B_84) | ~v5_orders_2(B_84) | ~v4_orders_2(B_84) | ~v3_orders_2(B_84) | v2_struct_0(B_84))), inference(negUnitSimplification, [status(thm)], [c_66, c_463])).
% 3.64/1.80  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.80  tff(c_593, plain, (![B_91, A_92]: (a_2_1_orders_2(B_91, k1_xboole_0)=A_92 | ~m1_subset_1(a_2_1_orders_2(B_91, k1_xboole_0), k1_zfmisc_1(A_92)) | ~m1_subset_1('#skF_1'(A_92, a_2_1_orders_2(B_91, k1_xboole_0)), u1_struct_0(B_91)) | ~l1_orders_2(B_91) | ~v5_orders_2(B_91) | ~v4_orders_2(B_91) | ~v3_orders_2(B_91) | v2_struct_0(B_91))), inference(resolution, [status(thm)], [c_493, c_4])).
% 3.64/1.80  tff(c_599, plain, (![B_93]: (~l1_orders_2(B_93) | ~v5_orders_2(B_93) | ~v4_orders_2(B_93) | ~v3_orders_2(B_93) | v2_struct_0(B_93) | a_2_1_orders_2(B_93, k1_xboole_0)=u1_struct_0(B_93) | ~m1_subset_1(a_2_1_orders_2(B_93, k1_xboole_0), k1_zfmisc_1(u1_struct_0(B_93))))), inference(resolution, [status(thm)], [c_6, c_593])).
% 3.64/1.80  tff(c_602, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_124, c_599])).
% 3.64/1.80  tff(c_605, plain, (v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_602])).
% 3.64/1.80  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_44, c_605])).
% 3.64/1.80  tff(c_608, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_65])).
% 3.64/1.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.64/1.80  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_608, c_2])).
% 3.64/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.80  
% 3.64/1.80  Inference rules
% 3.64/1.80  ----------------------
% 3.64/1.80  #Ref     : 0
% 3.64/1.80  #Sup     : 117
% 3.64/1.80  #Fact    : 0
% 3.64/1.80  #Define  : 0
% 3.64/1.80  #Split   : 2
% 3.64/1.80  #Chain   : 0
% 3.64/1.80  #Close   : 0
% 3.64/1.80  
% 3.64/1.80  Ordering : KBO
% 3.64/1.80  
% 3.64/1.80  Simplification rules
% 3.64/1.80  ----------------------
% 3.64/1.80  #Subsume      : 21
% 3.64/1.80  #Demod        : 266
% 3.64/1.80  #Tautology    : 31
% 3.64/1.80  #SimpNegUnit  : 53
% 3.64/1.80  #BackRed      : 3
% 3.64/1.80  
% 3.64/1.80  #Partial instantiations: 0
% 3.64/1.80  #Strategies tried      : 1
% 3.64/1.80  
% 3.64/1.80  Timing (in seconds)
% 3.64/1.80  ----------------------
% 3.64/1.81  Preprocessing        : 0.45
% 3.64/1.81  Parsing              : 0.21
% 3.64/1.81  CNF conversion       : 0.04
% 3.64/1.81  Main loop            : 0.57
% 3.64/1.81  Inferencing          : 0.20
% 3.64/1.81  Reduction            : 0.19
% 3.64/1.81  Demodulation         : 0.14
% 3.64/1.81  BG Simplification    : 0.03
% 3.64/1.81  Subsumption          : 0.11
% 3.64/1.81  Abstraction          : 0.04
% 3.64/1.81  MUC search           : 0.00
% 3.64/1.81  Cooper               : 0.00
% 3.64/1.81  Total                : 1.08
% 3.64/1.81  Index Insertion      : 0.00
% 3.64/1.81  Index Deletion       : 0.00
% 3.64/1.81  Index Matching       : 0.00
% 3.64/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
