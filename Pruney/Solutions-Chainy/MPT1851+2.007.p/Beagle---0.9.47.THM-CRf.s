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
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 137 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 298 expanded)
%              Number of equality atoms :   47 ( 128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_15] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_15)) = u1_pre_topc(A_15)
      | ~ v2_tdlat_3(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_112,plain,(
    ! [A_32] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_32)) = u1_pre_topc(A_32)
      | ~ v2_tdlat_3(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_4,B_5] : k3_tarski(k2_tarski(A_4,B_5)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_xboole_0,u1_struct_0(A_32)) = k3_tarski(u1_pre_topc(A_32))
      | ~ v2_tdlat_3(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_6])).

tff(c_147,plain,(
    ! [A_34] :
      ( k3_tarski(u1_pre_topc(A_34)) = u1_struct_0(A_34)
      | ~ v2_tdlat_3(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_124])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_34] :
      ( r1_tarski(u1_pre_topc(A_34),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v2_tdlat_3(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_8])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_212,plain,(
    ! [D_43,B_44,C_45,A_46] :
      ( D_43 = B_44
      | g1_pre_topc(C_45,D_43) != g1_pre_topc(A_46,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    ! [B_50,A_51] :
      ( u1_pre_topc('#skF_2') = B_50
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_51,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_212])).

tff(c_274,plain,(
    ! [A_7,A_51] :
      ( u1_pre_topc('#skF_2') = A_7
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_51,A_7)
      | ~ r1_tarski(A_7,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_12,c_269])).

tff(c_447,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_274])).

tff(c_452,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_455,plain,
    ( ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_156,c_452])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_455])).

tff(c_461,plain,(
    r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_171,plain,(
    ! [C_36,A_37,D_38,B_39] :
      ( C_36 = A_37
      | g1_pre_topc(C_36,D_38) != g1_pre_topc(A_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_316,plain,(
    ! [A_54,B_55] :
      ( u1_struct_0('#skF_2') = A_54
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_171])).

tff(c_321,plain,(
    ! [A_54,A_7] :
      ( u1_struct_0('#skF_2') = A_54
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_54,A_7)
      | ~ r1_tarski(A_7,k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_12,c_316])).

tff(c_620,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_321])).

tff(c_622,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_620])).

tff(c_460,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_216,plain,(
    ! [D_43,C_45] :
      ( u1_pre_topc('#skF_2') = D_43
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_45,D_43)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_212])).

tff(c_432,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_436,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_12,c_432])).

tff(c_463,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_436])).

tff(c_629,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_463])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_629])).

tff(c_636,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_175,plain,(
    ! [C_36,D_38] :
      ( u1_struct_0('#skF_2') = C_36
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_36,D_38)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_171])).

tff(c_660,plain,(
    ! [C_36,D_38] :
      ( u1_struct_0('#skF_2') = C_36
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_36,D_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_175])).

tff(c_663,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_660])).

tff(c_18,plain,(
    ! [A_15] :
      ( v2_tdlat_3(A_15)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_15)) != u1_pre_topc(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_686,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_18])).

tff(c_699,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_686])).

tff(c_700,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_699])).

tff(c_710,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_700])).

tff(c_712,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_710])).

tff(c_635,plain,(
    ! [D_43,C_45] :
      ( u1_pre_topc('#skF_2') = D_43
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_45,D_43) ) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_725,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_635])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.45  
% 2.50/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.45  %$ r1_tarski > m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.50/1.45  
% 2.50/1.45  %Foreground sorts:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Background operators:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Foreground operators:
% 2.50/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.50/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.45  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.50/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.45  
% 2.92/1.46  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tex_2)).
% 2.92/1.46  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tdlat_3)).
% 2.92/1.46  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.92/1.46  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.92/1.46  tff(f_33, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.92/1.46  tff(f_35, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.92/1.46  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.46  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.92/1.46  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.46  tff(c_24, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.46  tff(c_20, plain, (![A_15]: (k2_tarski(k1_xboole_0, u1_struct_0(A_15))=u1_pre_topc(A_15) | ~v2_tdlat_3(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.46  tff(c_22, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.46  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.46  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.46  tff(c_46, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.46  tff(c_54, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_46])).
% 2.92/1.46  tff(c_112, plain, (![A_32]: (k2_tarski(k1_xboole_0, u1_struct_0(A_32))=u1_pre_topc(A_32) | ~v2_tdlat_3(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.46  tff(c_6, plain, (![A_4, B_5]: (k3_tarski(k2_tarski(A_4, B_5))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.46  tff(c_124, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, u1_struct_0(A_32))=k3_tarski(u1_pre_topc(A_32)) | ~v2_tdlat_3(A_32) | ~l1_pre_topc(A_32))), inference(superposition, [status(thm), theory('equality')], [c_112, c_6])).
% 2.92/1.46  tff(c_147, plain, (![A_34]: (k3_tarski(u1_pre_topc(A_34))=u1_struct_0(A_34) | ~v2_tdlat_3(A_34) | ~l1_pre_topc(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_124])).
% 2.92/1.46  tff(c_8, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.46  tff(c_156, plain, (![A_34]: (r1_tarski(u1_pre_topc(A_34), k1_zfmisc_1(u1_struct_0(A_34))) | ~v2_tdlat_3(A_34) | ~l1_pre_topc(A_34))), inference(superposition, [status(thm), theory('equality')], [c_147, c_8])).
% 2.92/1.46  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.46  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.46  tff(c_212, plain, (![D_43, B_44, C_45, A_46]: (D_43=B_44 | g1_pre_topc(C_45, D_43)!=g1_pre_topc(A_46, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.46  tff(c_269, plain, (![B_50, A_51]: (u1_pre_topc('#skF_2')=B_50 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_51, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_212])).
% 2.92/1.46  tff(c_274, plain, (![A_7, A_51]: (u1_pre_topc('#skF_2')=A_7 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_51, A_7) | ~r1_tarski(A_7, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_12, c_269])).
% 2.92/1.46  tff(c_447, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_274])).
% 2.92/1.46  tff(c_452, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_447])).
% 2.92/1.46  tff(c_455, plain, (~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_156, c_452])).
% 2.92/1.46  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_455])).
% 2.92/1.46  tff(c_461, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_447])).
% 2.92/1.46  tff(c_171, plain, (![C_36, A_37, D_38, B_39]: (C_36=A_37 | g1_pre_topc(C_36, D_38)!=g1_pre_topc(A_37, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.46  tff(c_316, plain, (![A_54, B_55]: (u1_struct_0('#skF_2')=A_54 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_171])).
% 2.92/1.46  tff(c_321, plain, (![A_54, A_7]: (u1_struct_0('#skF_2')=A_54 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_54, A_7) | ~r1_tarski(A_7, k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_12, c_316])).
% 2.92/1.46  tff(c_620, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_321])).
% 2.92/1.46  tff(c_622, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_620])).
% 2.92/1.46  tff(c_460, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_447])).
% 2.92/1.46  tff(c_216, plain, (![D_43, C_45]: (u1_pre_topc('#skF_2')=D_43 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_45, D_43) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_212])).
% 2.92/1.46  tff(c_432, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_216])).
% 2.92/1.46  tff(c_436, plain, (~r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_432])).
% 2.92/1.46  tff(c_463, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_436])).
% 2.92/1.46  tff(c_629, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_463])).
% 2.92/1.46  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_629])).
% 2.92/1.46  tff(c_636, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_216])).
% 2.92/1.46  tff(c_175, plain, (![C_36, D_38]: (u1_struct_0('#skF_2')=C_36 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_36, D_38) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_171])).
% 2.92/1.46  tff(c_660, plain, (![C_36, D_38]: (u1_struct_0('#skF_2')=C_36 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_36, D_38))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_175])).
% 2.92/1.46  tff(c_663, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_660])).
% 2.92/1.46  tff(c_18, plain, (![A_15]: (v2_tdlat_3(A_15) | k2_tarski(k1_xboole_0, u1_struct_0(A_15))!=u1_pre_topc(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.46  tff(c_686, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_663, c_18])).
% 2.92/1.46  tff(c_699, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_686])).
% 2.92/1.46  tff(c_700, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_699])).
% 2.92/1.46  tff(c_710, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_700])).
% 2.92/1.46  tff(c_712, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_710])).
% 2.92/1.46  tff(c_635, plain, (![D_43, C_45]: (u1_pre_topc('#skF_2')=D_43 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_45, D_43))), inference(splitRight, [status(thm)], [c_216])).
% 2.92/1.46  tff(c_725, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_635])).
% 2.92/1.46  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_712, c_725])).
% 2.92/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.46  
% 2.92/1.46  Inference rules
% 2.92/1.46  ----------------------
% 2.92/1.46  #Ref     : 6
% 2.92/1.46  #Sup     : 162
% 2.92/1.46  #Fact    : 0
% 2.92/1.46  #Define  : 0
% 2.92/1.46  #Split   : 2
% 2.92/1.46  #Chain   : 0
% 2.92/1.46  #Close   : 0
% 2.92/1.46  
% 2.92/1.46  Ordering : KBO
% 2.92/1.46  
% 2.92/1.46  Simplification rules
% 2.92/1.46  ----------------------
% 2.92/1.46  #Subsume      : 22
% 2.92/1.46  #Demod        : 105
% 2.92/1.46  #Tautology    : 61
% 2.92/1.46  #SimpNegUnit  : 2
% 2.92/1.46  #BackRed      : 13
% 2.92/1.46  
% 2.92/1.46  #Partial instantiations: 0
% 2.92/1.46  #Strategies tried      : 1
% 2.92/1.46  
% 2.92/1.46  Timing (in seconds)
% 2.92/1.46  ----------------------
% 2.92/1.47  Preprocessing        : 0.28
% 2.92/1.47  Parsing              : 0.15
% 2.92/1.47  CNF conversion       : 0.02
% 2.92/1.47  Main loop            : 0.35
% 2.92/1.47  Inferencing          : 0.12
% 2.92/1.47  Reduction            : 0.13
% 2.92/1.47  Demodulation         : 0.10
% 2.92/1.47  BG Simplification    : 0.02
% 2.92/1.47  Subsumption          : 0.06
% 2.92/1.47  Abstraction          : 0.02
% 2.92/1.47  MUC search           : 0.00
% 2.92/1.47  Cooper               : 0.00
% 2.92/1.47  Total                : 0.66
% 2.92/1.47  Index Insertion      : 0.00
% 2.92/1.47  Index Deletion       : 0.00
% 2.92/1.47  Index Matching       : 0.00
% 2.92/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
