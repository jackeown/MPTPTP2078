%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 214 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 635 expanded)
%              Number of equality atoms :    7 (  66 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_111,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_70,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_38])).

tff(c_93,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_93])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_13] :
      ( v4_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_3')
      | ~ r2_hidden('#skF_2',D_26)
      | ~ v4_pre_topc(D_26,'#skF_1')
      | ~ v3_pre_topc(D_26,'#skF_1')
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_218,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,'#skF_3')
      | ~ r2_hidden('#skF_2',D_62)
      | ~ v4_pre_topc(D_62,'#skF_1')
      | ~ v3_pre_topc(D_62,'#skF_1')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_46])).

tff(c_280,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,'#skF_3')
      | ~ r2_hidden('#skF_2',A_78)
      | ~ v4_pre_topc(A_78,'#skF_1')
      | ~ v3_pre_topc(A_78,'#skF_1')
      | ~ r1_tarski(A_78,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_218])).

tff(c_289,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_280])).

tff(c_290,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_296,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_290])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_296])).

tff(c_302,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_304,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_307,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_310,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_307])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_310])).

tff(c_313,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_344,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_350,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_344])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_350])).

tff(c_356,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_162,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_171,plain,(
    ! [A_54,B_6,A_5] :
      ( m1_subset_1(A_54,B_6)
      | ~ r2_hidden(A_54,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_389,plain,(
    ! [B_80] :
      ( m1_subset_1(k2_struct_0('#skF_1'),B_80)
      | ~ r1_tarski('#skF_3',B_80) ) ),
    inference(resolution,[status(thm)],[c_356,c_171])).

tff(c_16,plain,(
    ! [B_4,A_3] :
      ( v1_xboole_0(B_4)
      | ~ m1_subset_1(B_4,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_399,plain,(
    ! [B_80] :
      ( v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ v1_xboole_0(B_80)
      | ~ r1_tarski('#skF_3',B_80) ) ),
    inference(resolution,[status(thm)],[c_389,c_16])).

tff(c_412,plain,(
    ! [B_81] :
      ( ~ v1_xboole_0(B_81)
      | ~ r1_tarski('#skF_3',B_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_399])).

tff(c_423,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_412])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_423])).

tff(c_431,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_432,plain,(
    ! [A_82] :
      ( ~ v1_xboole_0(u1_struct_0(A_82))
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_435,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_432])).

tff(c_437,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_435])).

tff(c_438,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_437])).

tff(c_441,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_438])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.34  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.34  
% 2.50/1.34  %Foreground sorts:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Background operators:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Foreground operators:
% 2.50/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.50/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.50/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.34  
% 2.67/1.36  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.67/1.36  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.67/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.67/1.36  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.36  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.67/1.36  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.67/1.36  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.67/1.36  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.67/1.36  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.36  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.67/1.36  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.67/1.36  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_26, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.36  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_34, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.67/1.36  tff(c_54, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 2.67/1.36  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.36  tff(c_61, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.36  tff(c_66, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_26, c_61])).
% 2.67/1.36  tff(c_70, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_66])).
% 2.67/1.36  tff(c_38, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_72, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_38])).
% 2.67/1.36  tff(c_93, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.36  tff(c_110, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_93])).
% 2.67/1.36  tff(c_123, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.67/1.36  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_30, plain, (![A_13]: (v4_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.67/1.36  tff(c_12, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.36  tff(c_32, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.67/1.36  tff(c_20, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.36  tff(c_46, plain, (![D_26]: (r2_hidden(D_26, '#skF_3') | ~r2_hidden('#skF_2', D_26) | ~v4_pre_topc(D_26, '#skF_1') | ~v3_pre_topc(D_26, '#skF_1') | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.67/1.36  tff(c_218, plain, (![D_62]: (r2_hidden(D_62, '#skF_3') | ~r2_hidden('#skF_2', D_62) | ~v4_pre_topc(D_62, '#skF_1') | ~v3_pre_topc(D_62, '#skF_1') | ~m1_subset_1(D_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_46])).
% 2.67/1.36  tff(c_280, plain, (![A_78]: (r2_hidden(A_78, '#skF_3') | ~r2_hidden('#skF_2', A_78) | ~v4_pre_topc(A_78, '#skF_1') | ~v3_pre_topc(A_78, '#skF_1') | ~r1_tarski(A_78, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_218])).
% 2.67/1.36  tff(c_289, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_8, c_280])).
% 2.67/1.36  tff(c_290, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_289])).
% 2.67/1.36  tff(c_296, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_290])).
% 2.67/1.36  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_296])).
% 2.67/1.36  tff(c_302, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_289])).
% 2.67/1.36  tff(c_304, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.67/1.36  tff(c_307, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_304])).
% 2.67/1.36  tff(c_310, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_307])).
% 2.67/1.36  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_310])).
% 2.67/1.36  tff(c_313, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_302])).
% 2.67/1.36  tff(c_344, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_313])).
% 2.67/1.36  tff(c_350, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_344])).
% 2.67/1.36  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_350])).
% 2.67/1.36  tff(c_356, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_313])).
% 2.67/1.36  tff(c_162, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.36  tff(c_171, plain, (![A_54, B_6, A_5]: (m1_subset_1(A_54, B_6) | ~r2_hidden(A_54, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_20, c_162])).
% 2.67/1.36  tff(c_389, plain, (![B_80]: (m1_subset_1(k2_struct_0('#skF_1'), B_80) | ~r1_tarski('#skF_3', B_80))), inference(resolution, [status(thm)], [c_356, c_171])).
% 2.67/1.36  tff(c_16, plain, (![B_4, A_3]: (v1_xboole_0(B_4) | ~m1_subset_1(B_4, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.36  tff(c_399, plain, (![B_80]: (v1_xboole_0(k2_struct_0('#skF_1')) | ~v1_xboole_0(B_80) | ~r1_tarski('#skF_3', B_80))), inference(resolution, [status(thm)], [c_389, c_16])).
% 2.67/1.36  tff(c_412, plain, (![B_81]: (~v1_xboole_0(B_81) | ~r1_tarski('#skF_3', B_81))), inference(negUnitSimplification, [status(thm)], [c_123, c_399])).
% 2.67/1.36  tff(c_423, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_412])).
% 2.67/1.36  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_423])).
% 2.67/1.36  tff(c_431, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_110])).
% 2.67/1.36  tff(c_432, plain, (![A_82]: (~v1_xboole_0(u1_struct_0(A_82)) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.36  tff(c_435, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_432])).
% 2.67/1.36  tff(c_437, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_435])).
% 2.67/1.36  tff(c_438, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_437])).
% 2.67/1.36  tff(c_441, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_438])).
% 2.67/1.36  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_441])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 75
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 7
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 15
% 2.67/1.36  #Demod        : 34
% 2.67/1.36  #Tautology    : 28
% 2.67/1.36  #SimpNegUnit  : 6
% 2.67/1.36  #BackRed      : 2
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.36  Preprocessing        : 0.32
% 2.67/1.36  Parsing              : 0.17
% 2.67/1.36  CNF conversion       : 0.02
% 2.67/1.36  Main loop            : 0.27
% 2.67/1.36  Inferencing          : 0.10
% 2.67/1.37  Reduction            : 0.08
% 2.67/1.37  Demodulation         : 0.05
% 2.67/1.37  BG Simplification    : 0.01
% 2.67/1.37  Subsumption          : 0.05
% 2.67/1.37  Abstraction          : 0.01
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.63
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
