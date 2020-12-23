%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 194 expanded)
%              Number of equality atoms :   40 (  80 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_20] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_20)) = u1_pre_topc(A_20)
      | ~ v2_tdlat_3(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [B_3,A_2] : k2_tarski(B_3,A_2) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_37] : k2_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_278,plain,(
    ! [A_47] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_47)) = u1_pre_topc(A_47)
      | ~ v2_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(A_11,k1_zfmisc_1(k3_tarski(A_11))) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_32,B_33] : r1_tarski(k2_tarski(A_32,B_33),k1_zfmisc_1(k2_xboole_0(A_32,B_33))) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_287,plain,(
    ! [A_47] :
      ( r1_tarski(u1_pre_topc(A_47),k1_zfmisc_1(k2_xboole_0(k1_xboole_0,u1_struct_0(A_47))))
      | ~ v2_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_103])).

tff(c_301,plain,(
    ! [A_47] :
      ( r1_tarski(u1_pre_topc(A_47),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ v2_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_287])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_366,plain,(
    ! [C_55,A_56,D_57,B_58] :
      ( C_55 = A_56
      | g1_pre_topc(C_55,D_57) != g1_pre_topc(A_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_372,plain,(
    ! [A_60,B_61] :
      ( u1_struct_0('#skF_2') = A_60
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_366])).

tff(c_377,plain,(
    ! [A_60,A_12] :
      ( u1_struct_0('#skF_2') = A_60
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_60,A_12)
      | ~ r1_tarski(A_12,k1_zfmisc_1(A_60)) ) ),
    inference(resolution,[status(thm)],[c_16,c_372])).

tff(c_380,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_377])).

tff(c_386,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_389,plain,
    ( ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_301,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_389])).

tff(c_394,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_22,plain,(
    ! [A_20] :
      ( v2_tdlat_3(A_20)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_20)) != u1_pre_topc(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_414,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_22])).

tff(c_422,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_414])).

tff(c_423,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_422])).

tff(c_427,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_423])).

tff(c_429,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_427])).

tff(c_395,plain,(
    r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_341,plain,(
    ! [D_50,B_51,C_52,A_53] :
      ( D_50 = B_51
      | g1_pre_topc(C_52,D_50) != g1_pre_topc(A_53,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_396,plain,(
    ! [B_64,A_65] :
      ( u1_pre_topc('#skF_2') = B_64
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_65,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_341])).

tff(c_401,plain,(
    ! [A_12,A_65] :
      ( u1_pre_topc('#skF_2') = A_12
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_65,A_12)
      | ~ r1_tarski(A_12,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_16,c_396])).

tff(c_444,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_401])).

tff(c_446,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_444])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  %$ r1_tarski > m1_subset_1 > v2_tdlat_3 > l1_pre_topc > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.32/1.35  
% 2.32/1.35  %Foreground sorts:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Background operators:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Foreground operators:
% 2.32/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.35  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.32/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.35  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.32/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.35  
% 2.32/1.36  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tex_2)).
% 2.32/1.36  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tdlat_3)).
% 2.32/1.36  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.32/1.36  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.32/1.36  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.32/1.36  tff(f_37, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.32/1.36  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.32/1.36  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.32/1.36  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.36  tff(c_28, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.36  tff(c_24, plain, (![A_20]: (k2_tarski(k1_xboole_0, u1_struct_0(A_20))=u1_pre_topc(A_20) | ~v2_tdlat_3(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.36  tff(c_26, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.36  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.36  tff(c_4, plain, (![B_3, A_2]: (k2_tarski(B_3, A_2)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.36  tff(c_97, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.36  tff(c_115, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 2.32/1.36  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.36  tff(c_141, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_115, c_10])).
% 2.32/1.36  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.36  tff(c_157, plain, (![A_37]: (k2_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 2.32/1.36  tff(c_278, plain, (![A_47]: (k2_tarski(k1_xboole_0, u1_struct_0(A_47))=u1_pre_topc(A_47) | ~v2_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.36  tff(c_12, plain, (![A_11]: (r1_tarski(A_11, k1_zfmisc_1(k3_tarski(A_11))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.36  tff(c_103, plain, (![A_32, B_33]: (r1_tarski(k2_tarski(A_32, B_33), k1_zfmisc_1(k2_xboole_0(A_32, B_33))))), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 2.32/1.36  tff(c_287, plain, (![A_47]: (r1_tarski(u1_pre_topc(A_47), k1_zfmisc_1(k2_xboole_0(k1_xboole_0, u1_struct_0(A_47)))) | ~v2_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_278, c_103])).
% 2.32/1.36  tff(c_301, plain, (![A_47]: (r1_tarski(u1_pre_topc(A_47), k1_zfmisc_1(u1_struct_0(A_47))) | ~v2_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_287])).
% 2.32/1.36  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.36  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.36  tff(c_366, plain, (![C_55, A_56, D_57, B_58]: (C_55=A_56 | g1_pre_topc(C_55, D_57)!=g1_pre_topc(A_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.36  tff(c_372, plain, (![A_60, B_61]: (u1_struct_0('#skF_2')=A_60 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_366])).
% 2.32/1.36  tff(c_377, plain, (![A_60, A_12]: (u1_struct_0('#skF_2')=A_60 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_60, A_12) | ~r1_tarski(A_12, k1_zfmisc_1(A_60)))), inference(resolution, [status(thm)], [c_16, c_372])).
% 2.32/1.36  tff(c_380, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_377])).
% 2.32/1.36  tff(c_386, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_380])).
% 2.32/1.36  tff(c_389, plain, (~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_301, c_386])).
% 2.32/1.36  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_389])).
% 2.32/1.36  tff(c_394, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_380])).
% 2.32/1.36  tff(c_22, plain, (![A_20]: (v2_tdlat_3(A_20) | k2_tarski(k1_xboole_0, u1_struct_0(A_20))!=u1_pre_topc(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.36  tff(c_414, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_394, c_22])).
% 2.32/1.36  tff(c_422, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_414])).
% 2.32/1.36  tff(c_423, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_422])).
% 2.32/1.36  tff(c_427, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_423])).
% 2.32/1.36  tff(c_429, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_427])).
% 2.32/1.36  tff(c_395, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_380])).
% 2.32/1.36  tff(c_341, plain, (![D_50, B_51, C_52, A_53]: (D_50=B_51 | g1_pre_topc(C_52, D_50)!=g1_pre_topc(A_53, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.36  tff(c_396, plain, (![B_64, A_65]: (u1_pre_topc('#skF_2')=B_64 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_65, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_341])).
% 2.32/1.36  tff(c_401, plain, (![A_12, A_65]: (u1_pre_topc('#skF_2')=A_12 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_65, A_12) | ~r1_tarski(A_12, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_16, c_396])).
% 2.32/1.36  tff(c_444, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_401])).
% 2.32/1.36  tff(c_446, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_444])).
% 2.32/1.36  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_446])).
% 2.32/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  Inference rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Ref     : 4
% 2.32/1.36  #Sup     : 96
% 2.32/1.36  #Fact    : 0
% 2.32/1.36  #Define  : 0
% 2.32/1.36  #Split   : 1
% 2.32/1.36  #Chain   : 0
% 2.32/1.36  #Close   : 0
% 2.32/1.36  
% 2.32/1.36  Ordering : KBO
% 2.32/1.36  
% 2.32/1.36  Simplification rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Subsume      : 10
% 2.32/1.36  #Demod        : 39
% 2.32/1.36  #Tautology    : 69
% 2.32/1.36  #SimpNegUnit  : 2
% 2.32/1.36  #BackRed      : 3
% 2.32/1.36  
% 2.32/1.36  #Partial instantiations: 0
% 2.32/1.36  #Strategies tried      : 1
% 2.32/1.36  
% 2.32/1.36  Timing (in seconds)
% 2.32/1.36  ----------------------
% 2.32/1.36  Preprocessing        : 0.31
% 2.32/1.36  Parsing              : 0.17
% 2.32/1.36  CNF conversion       : 0.02
% 2.32/1.36  Main loop            : 0.24
% 2.32/1.36  Inferencing          : 0.09
% 2.32/1.36  Reduction            : 0.08
% 2.32/1.36  Demodulation         : 0.06
% 2.32/1.36  BG Simplification    : 0.01
% 2.32/1.36  Subsumption          : 0.04
% 2.32/1.36  Abstraction          : 0.01
% 2.32/1.37  MUC search           : 0.00
% 2.32/1.37  Cooper               : 0.00
% 2.32/1.37  Total                : 0.58
% 2.32/1.37  Index Insertion      : 0.00
% 2.32/1.37  Index Deletion       : 0.00
% 2.32/1.37  Index Matching       : 0.00
% 2.32/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
