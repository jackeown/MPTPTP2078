%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1150+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:30 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  111 (1285 expanded)
%              Number of leaves         :   37 ( 463 expanded)
%              Depth                    :   22
%              Number of atoms          :  260 (3921 expanded)
%              Number of equality atoms :   28 ( 634 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_61,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_69,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_97,plain,(
    ! [A_50] :
      ( m1_subset_1(k2_struct_0(A_50),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_97])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_108,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_114,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_113,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_204,plain,(
    ! [A_75,B_76] :
      ( k1_orders_2(A_75,B_76) = a_2_0_orders_2(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [B_76] :
      ( k1_orders_2('#skF_4',B_76) = a_2_0_orders_2('#skF_4',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_204])).

tff(c_227,plain,(
    ! [B_76] :
      ( k1_orders_2('#skF_4',B_76) = a_2_0_orders_2('#skF_4',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_218])).

tff(c_230,plain,(
    ! [B_77] :
      ( k1_orders_2('#skF_4',B_77) = a_2_0_orders_2('#skF_4',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_227])).

tff(c_247,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_113,c_230])).

tff(c_44,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_250,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_44])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_290,plain,(
    ! [A_82,B_83,C_84] :
      ( '#skF_2'(A_82,B_83,C_84) = A_82
      | ~ r2_hidden(A_82,a_2_0_orders_2(B_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(B_83)))
      | ~ l1_orders_2(B_83)
      | ~ v5_orders_2(B_83)
      | ~ v4_orders_2(B_83)
      | ~ v3_orders_2(B_83)
      | v2_struct_0(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1094,plain,(
    ! [A_156,B_157,C_158] :
      ( '#skF_2'(A_156,B_157,C_158) = A_156
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(B_157)))
      | ~ l1_orders_2(B_157)
      | ~ v5_orders_2(B_157)
      | ~ v4_orders_2(B_157)
      | ~ v3_orders_2(B_157)
      | v2_struct_0(B_157)
      | v1_xboole_0(a_2_0_orders_2(B_157,C_158))
      | ~ m1_subset_1(A_156,a_2_0_orders_2(B_157,C_158)) ) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_1116,plain,(
    ! [A_156,C_158] :
      ( '#skF_2'(A_156,'#skF_4',C_158) = A_156
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(a_2_0_orders_2('#skF_4',C_158))
      | ~ m1_subset_1(A_156,a_2_0_orders_2('#skF_4',C_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1094])).

tff(c_1128,plain,(
    ! [A_156,C_158] :
      ( '#skF_2'(A_156,'#skF_4',C_158) = A_156
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v1_xboole_0(a_2_0_orders_2('#skF_4',C_158))
      | ~ m1_subset_1(A_156,a_2_0_orders_2('#skF_4',C_158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1116])).

tff(c_1131,plain,(
    ! [A_159,C_160] :
      ( '#skF_2'(A_159,'#skF_4',C_160) = A_159
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v1_xboole_0(a_2_0_orders_2('#skF_4',C_160))
      | ~ m1_subset_1(A_159,a_2_0_orders_2('#skF_4',C_160)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1128])).

tff(c_1165,plain,(
    ! [A_159] :
      ( '#skF_2'(A_159,'#skF_4',k2_struct_0('#skF_4')) = A_159
      | v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(A_159,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_113,c_1131])).

tff(c_1168,plain,(
    v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1165])).

tff(c_42,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1171,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1168,c_42])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_1171])).

tff(c_1177,plain,(
    ~ v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1198,plain,(
    ! [A_164] :
      ( '#skF_2'(A_164,'#skF_4',k2_struct_0('#skF_4')) = A_164
      | ~ m1_subset_1(A_164,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_1228,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_16,c_1198])).

tff(c_389,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1('#skF_2'(A_88,B_89,C_90),u1_struct_0(B_89))
      | ~ r2_hidden(A_88,a_2_0_orders_2(B_89,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ l1_orders_2(B_89)
      | ~ v5_orders_2(B_89)
      | ~ v4_orders_2(B_89)
      | ~ v3_orders_2(B_89)
      | v2_struct_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_392,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_0_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_389])).

tff(c_394,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_0_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_69,c_392])).

tff(c_395,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_0_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_394])).

tff(c_1242,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_395])).

tff(c_1251,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1242])).

tff(c_1355,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1251])).

tff(c_1359,plain,
    ( v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_34,c_1355])).

tff(c_1362,plain,(
    v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1359])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1177,c_1362])).

tff(c_1365,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1251])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1366,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1251])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1287,plain,(
    ! [A_167,A_168] :
      ( '#skF_2'(A_167,'#skF_4',A_168) = A_167
      | v1_xboole_0(a_2_0_orders_2('#skF_4',A_168))
      | ~ m1_subset_1(A_167,a_2_0_orders_2('#skF_4',A_168))
      | ~ r1_tarski(A_168,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1131])).

tff(c_1571,plain,(
    ! [A_179] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',A_179)),'#skF_4',A_179) = '#skF_1'(a_2_0_orders_2('#skF_4',A_179))
      | v1_xboole_0(a_2_0_orders_2('#skF_4',A_179))
      | ~ r1_tarski(A_179,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1287])).

tff(c_688,plain,(
    ! [B_126,E_127,A_128,C_129] :
      ( r2_orders_2(B_126,E_127,'#skF_2'(A_128,B_126,C_129))
      | ~ r2_hidden(E_127,C_129)
      | ~ m1_subset_1(E_127,u1_struct_0(B_126))
      | ~ r2_hidden(A_128,a_2_0_orders_2(B_126,C_129))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(B_126)))
      | ~ l1_orders_2(B_126)
      | ~ v5_orders_2(B_126)
      | ~ v4_orders_2(B_126)
      | ~ v3_orders_2(B_126)
      | v2_struct_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_701,plain,(
    ! [E_127,A_128,C_129] :
      ( r2_orders_2('#skF_4',E_127,'#skF_2'(A_128,'#skF_4',C_129))
      | ~ r2_hidden(E_127,C_129)
      | ~ m1_subset_1(E_127,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_128,a_2_0_orders_2('#skF_4',C_129))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_688])).

tff(c_710,plain,(
    ! [E_127,A_128,C_129] :
      ( r2_orders_2('#skF_4',E_127,'#skF_2'(A_128,'#skF_4',C_129))
      | ~ r2_hidden(E_127,C_129)
      | ~ m1_subset_1(E_127,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_128,a_2_0_orders_2('#skF_4',C_129))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_69,c_701])).

tff(c_751,plain,(
    ! [E_132,A_133,C_134] :
      ( r2_orders_2('#skF_4',E_132,'#skF_2'(A_133,'#skF_4',C_134))
      | ~ r2_hidden(E_132,C_134)
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_133,a_2_0_orders_2('#skF_4',C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_710])).

tff(c_773,plain,(
    ! [E_132,A_133] :
      ( r2_orders_2('#skF_4',E_132,'#skF_2'(A_133,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_132,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_133,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_113,c_751])).

tff(c_1591,plain,(
    ! [E_132] :
      ( r2_orders_2('#skF_4',E_132,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_132,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_773])).

tff(c_1614,plain,(
    ! [E_132] :
      ( r2_orders_2('#skF_4',E_132,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_132,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | v1_xboole_0(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1366,c_1591])).

tff(c_1625,plain,(
    ! [E_180] :
      ( r2_orders_2('#skF_4',E_180,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_180,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1177,c_1614])).

tff(c_32,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r2_orders_2(A_25,B_26,B_26)
      | ~ m1_subset_1(C_27,u1_struct_0(A_25))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1631,plain,(
    ! [C_27] :
      ( ~ m1_subset_1(C_27,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1625,c_32])).

tff(c_1638,plain,(
    ! [C_27] :
      ( ~ m1_subset_1(C_27,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_46,c_1365,c_69,c_69,c_1631])).

tff(c_1639,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1638])).

tff(c_1658,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_1639])).

tff(c_1661,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1658])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k2_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1664,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1661,c_18])).

tff(c_1670,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1664])).

tff(c_1672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1670])).

tff(c_1673,plain,(
    ! [C_27] : ~ m1_subset_1(C_27,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1638])).

tff(c_1688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1673,c_1365])).

%------------------------------------------------------------------------------
