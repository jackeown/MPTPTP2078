%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 325 expanded)
%              Number of leaves         :   30 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 940 expanded)
%              Number of equality atoms :    6 ( 117 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_73,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_32])).

tff(c_81,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_73,c_81])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_22,plain,(
    ! [A_10] :
      ( v4_pre_topc(k2_struct_0(A_10),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    ! [A_36] :
      ( m1_subset_1(k2_struct_0(A_36),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_108])).

tff(c_129,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_132,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_137,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_44,plain,(
    ! [D_24] :
      ( v4_pre_topc(D_24,'#skF_1')
      | ~ r2_hidden(D_24,'#skF_3')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_144,plain,(
    ! [D_24] :
      ( v4_pre_topc(D_24,'#skF_1')
      | ~ r2_hidden(D_24,'#skF_3')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44])).

tff(c_165,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_144])).

tff(c_170,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_40,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_3')
      | ~ r2_hidden('#skF_2',D_24)
      | ~ v4_pre_topc(D_24,'#skF_1')
      | ~ v3_pre_topc(D_24,'#skF_1')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_212,plain,(
    ! [D_51] :
      ( r2_hidden(D_51,'#skF_3')
      | ~ r2_hidden('#skF_2',D_51)
      | ~ v4_pre_topc(D_51,'#skF_1')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_40])).

tff(c_215,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_212])).

tff(c_226,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_215])).

tff(c_268,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_271,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_271])).

tff(c_276,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_278,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_281,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_278])).

tff(c_284,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_284])).

tff(c_287,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_311,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_287])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_311])).

tff(c_317,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_318,plain,(
    ! [A_60,C_61,B_62] :
      ( m1_subset_1(A_60,C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_337,plain,(
    ! [A_63,A_64] :
      ( m1_subset_1(A_63,A_64)
      | ~ r2_hidden(A_63,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_47,c_318])).

tff(c_367,plain,(
    ! [A_66] : m1_subset_1(k2_struct_0('#skF_1'),A_66) ),
    inference(resolution,[status(thm)],[c_317,c_337])).

tff(c_10,plain,(
    ! [B_2,A_1] :
      ( v1_xboole_0(B_2)
      | ~ m1_subset_1(B_2,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_385,plain,(
    ! [A_66] :
      ( v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_367,c_10])).

tff(c_398,plain,(
    ! [A_66] : ~ v1_xboole_0(A_66) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_385])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_49,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_49])).

tff(c_405,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_24,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k2_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_408,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_405,c_24])).

tff(c_411,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_408])).

tff(c_414,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:35:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.29  
% 2.41/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.29  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.29  
% 2.41/1.29  %Foreground sorts:
% 2.41/1.29  
% 2.41/1.29  
% 2.41/1.29  %Background operators:
% 2.41/1.29  
% 2.41/1.29  
% 2.41/1.29  %Foreground operators:
% 2.41/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.41/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.29  
% 2.41/1.31  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.41/1.31  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.41/1.31  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.41/1.31  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.41/1.31  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.41/1.31  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.41/1.31  tff(f_55, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.41/1.31  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.41/1.31  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.41/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.31  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.41/1.31  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_20, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.41/1.31  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_56, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.31  tff(c_67, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.41/1.31  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.41/1.31  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_73, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_32])).
% 2.41/1.31  tff(c_81, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.31  tff(c_92, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_73, c_81])).
% 2.41/1.31  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.41/1.31  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_22, plain, (![A_10]: (v4_pre_topc(k2_struct_0(A_10), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.31  tff(c_6, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.31  tff(c_26, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.41/1.31  tff(c_108, plain, (![A_36]: (m1_subset_1(k2_struct_0(A_36), k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.41/1.31  tff(c_114, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_71, c_108])).
% 2.41/1.31  tff(c_129, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 2.41/1.31  tff(c_132, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_129])).
% 2.41/1.31  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_132])).
% 2.41/1.31  tff(c_137, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_114])).
% 2.41/1.31  tff(c_44, plain, (![D_24]: (v4_pre_topc(D_24, '#skF_1') | ~r2_hidden(D_24, '#skF_3') | ~m1_subset_1(D_24, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_144, plain, (![D_24]: (v4_pre_topc(D_24, '#skF_1') | ~r2_hidden(D_24, '#skF_3') | ~m1_subset_1(D_24, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_44])).
% 2.41/1.31  tff(c_165, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_137, c_144])).
% 2.41/1.31  tff(c_170, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_165])).
% 2.41/1.31  tff(c_40, plain, (![D_24]: (r2_hidden(D_24, '#skF_3') | ~r2_hidden('#skF_2', D_24) | ~v4_pre_topc(D_24, '#skF_1') | ~v3_pre_topc(D_24, '#skF_1') | ~m1_subset_1(D_24, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_212, plain, (![D_51]: (r2_hidden(D_51, '#skF_3') | ~r2_hidden('#skF_2', D_51) | ~v4_pre_topc(D_51, '#skF_1') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_40])).
% 2.41/1.31  tff(c_215, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_137, c_212])).
% 2.41/1.31  tff(c_226, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_170, c_215])).
% 2.41/1.31  tff(c_268, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_226])).
% 2.41/1.31  tff(c_271, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_268])).
% 2.41/1.31  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_271])).
% 2.41/1.31  tff(c_276, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_226])).
% 2.41/1.31  tff(c_278, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_276])).
% 2.41/1.31  tff(c_281, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_278])).
% 2.41/1.31  tff(c_284, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_281])).
% 2.41/1.31  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_284])).
% 2.41/1.31  tff(c_287, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_276])).
% 2.41/1.31  tff(c_311, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_287])).
% 2.41/1.31  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_311])).
% 2.41/1.31  tff(c_317, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_165])).
% 2.41/1.31  tff(c_28, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.41/1.31  tff(c_12, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.31  tff(c_47, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 2.41/1.31  tff(c_318, plain, (![A_60, C_61, B_62]: (m1_subset_1(A_60, C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.31  tff(c_337, plain, (![A_63, A_64]: (m1_subset_1(A_63, A_64) | ~r2_hidden(A_63, '#skF_3'))), inference(resolution, [status(thm)], [c_47, c_318])).
% 2.41/1.31  tff(c_367, plain, (![A_66]: (m1_subset_1(k2_struct_0('#skF_1'), A_66))), inference(resolution, [status(thm)], [c_317, c_337])).
% 2.41/1.31  tff(c_10, plain, (![B_2, A_1]: (v1_xboole_0(B_2) | ~m1_subset_1(B_2, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.31  tff(c_385, plain, (![A_66]: (v1_xboole_0(k2_struct_0('#skF_1')) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_367, c_10])).
% 2.41/1.31  tff(c_398, plain, (![A_66]: (~v1_xboole_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_95, c_385])).
% 2.41/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.41/1.31  tff(c_49, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2])).
% 2.41/1.31  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_398, c_49])).
% 2.41/1.31  tff(c_405, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_92])).
% 2.41/1.31  tff(c_24, plain, (![A_11]: (~v1_xboole_0(k2_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.31  tff(c_408, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_405, c_24])).
% 2.41/1.31  tff(c_411, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_408])).
% 2.41/1.31  tff(c_414, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_411])).
% 2.41/1.31  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_414])).
% 2.41/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  Inference rules
% 2.41/1.31  ----------------------
% 2.41/1.31  #Ref     : 0
% 2.41/1.31  #Sup     : 65
% 2.41/1.31  #Fact    : 0
% 2.41/1.31  #Define  : 0
% 2.41/1.31  #Split   : 7
% 2.41/1.31  #Chain   : 0
% 2.41/1.31  #Close   : 0
% 2.41/1.31  
% 2.41/1.31  Ordering : KBO
% 2.41/1.31  
% 2.41/1.31  Simplification rules
% 2.41/1.31  ----------------------
% 2.41/1.31  #Subsume      : 17
% 2.41/1.31  #Demod        : 38
% 2.41/1.31  #Tautology    : 24
% 2.41/1.31  #SimpNegUnit  : 15
% 2.41/1.31  #BackRed      : 5
% 2.41/1.31  
% 2.41/1.31  #Partial instantiations: 0
% 2.41/1.31  #Strategies tried      : 1
% 2.41/1.31  
% 2.41/1.31  Timing (in seconds)
% 2.41/1.31  ----------------------
% 2.41/1.31  Preprocessing        : 0.31
% 2.41/1.31  Parsing              : 0.16
% 2.41/1.31  CNF conversion       : 0.02
% 2.41/1.31  Main loop            : 0.24
% 2.41/1.31  Inferencing          : 0.09
% 2.41/1.31  Reduction            : 0.07
% 2.41/1.31  Demodulation         : 0.05
% 2.41/1.31  BG Simplification    : 0.01
% 2.41/1.31  Subsumption          : 0.04
% 2.41/1.31  Abstraction          : 0.01
% 2.41/1.31  MUC search           : 0.00
% 2.41/1.31  Cooper               : 0.00
% 2.41/1.31  Total                : 0.59
% 2.41/1.31  Index Insertion      : 0.00
% 2.41/1.31  Index Deletion       : 0.00
% 2.41/1.31  Index Matching       : 0.00
% 2.41/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
