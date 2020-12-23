%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 216 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 666 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_455,plain,(
    ! [B_59,A_60] :
      ( l1_pre_topc(B_59)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_458,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_455])).

tff(c_467,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_458])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_461,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_455])).

tff(c_470,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_461])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    ! [B_29,A_30] :
      ( l1_pre_topc(B_29)
      | ~ m1_pre_topc(B_29,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_22,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_92,plain,(
    ! [B_33,A_34] :
      ( r1_tsep_1(B_33,A_34)
      | ~ r1_tsep_1(A_34,B_33)
      | ~ l1_struct_0(B_33)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_95,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_99])).

tff(c_105,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_41,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = k2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_45])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_71,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_62])).

tff(c_80,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_45])).

tff(c_297,plain,(
    ! [B_47,C_48,A_49] :
      ( r1_tarski(u1_struct_0(B_47),u1_struct_0(C_48))
      | ~ m1_pre_topc(B_47,C_48)
      | ~ m1_pre_topc(C_48,A_49)
      | ~ m1_pre_topc(B_47,A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_301,plain,(
    ! [B_47] :
      ( r1_tarski(u1_struct_0(B_47),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_47,'#skF_3')
      | ~ m1_pre_topc(B_47,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_297])).

tff(c_387,plain,(
    ! [B_54] :
      ( r1_tarski(u1_struct_0(B_54),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_80,c_301])).

tff(c_393,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_387])).

tff(c_400,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_393])).

tff(c_104,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_130,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_133,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_133])).

tff(c_139,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_170,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(u1_struct_0(A_37),u1_struct_0(B_38))
      | ~ r1_tsep_1(A_37,B_38)
      | ~ l1_struct_0(B_38)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_185,plain,(
    ! [B_38] :
      ( r1_xboole_0(k2_struct_0('#skF_2'),u1_struct_0(B_38))
      | ~ r1_tsep_1('#skF_2',B_38)
      | ~ l1_struct_0(B_38)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_170])).

tff(c_402,plain,(
    ! [B_55] :
      ( r1_xboole_0(k2_struct_0('#skF_2'),u1_struct_0(B_55))
      | ~ r1_tsep_1('#skF_2',B_55)
      | ~ l1_struct_0(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_185])).

tff(c_408,plain,
    ( r1_xboole_0(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_402])).

tff(c_417,plain,(
    r1_xboole_0(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_40,c_408])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_426,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_417,c_2])).

tff(c_429,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_426])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_432,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_429,c_10])).

tff(c_435,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_432])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_435])).

tff(c_439,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_438,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_491,plain,(
    ! [B_63,A_64] :
      ( r1_tsep_1(B_63,A_64)
      | ~ r1_tsep_1(A_64,B_63)
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_493,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_438,c_491])).

tff(c_496,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_493])).

tff(c_497,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_500,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_500])).

tff(c_505,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_532,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_505])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.43  
% 2.89/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.43  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.43  
% 2.89/1.43  %Foreground sorts:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Background operators:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Foreground operators:
% 2.89/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.89/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.89/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.43  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.89/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.89/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.43  
% 2.89/1.46  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.89/1.46  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.89/1.46  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.46  tff(f_73, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.89/1.46  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.89/1.46  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.89/1.46  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.89/1.46  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.89/1.46  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.89/1.46  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_455, plain, (![B_59, A_60]: (l1_pre_topc(B_59) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.89/1.46  tff(c_458, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_455])).
% 2.89/1.46  tff(c_467, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_458])).
% 2.89/1.46  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.46  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_461, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_455])).
% 2.89/1.46  tff(c_470, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_461])).
% 2.89/1.46  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_56, plain, (![B_29, A_30]: (l1_pre_topc(B_29) | ~m1_pre_topc(B_29, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.89/1.46  tff(c_59, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_56])).
% 2.89/1.46  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59])).
% 2.89/1.46  tff(c_22, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_40, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_22])).
% 2.89/1.46  tff(c_92, plain, (![B_33, A_34]: (r1_tsep_1(B_33, A_34) | ~r1_tsep_1(A_34, B_33) | ~l1_struct_0(B_33) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.89/1.46  tff(c_95, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_92])).
% 2.89/1.46  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_95])).
% 2.89/1.46  tff(c_99, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.89/1.46  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_99])).
% 2.89/1.46  tff(c_105, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_95])).
% 2.89/1.46  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_41, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.46  tff(c_45, plain, (![A_4]: (u1_struct_0(A_4)=k2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.89/1.46  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_45])).
% 2.89/1.46  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.46  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.89/1.46  tff(c_71, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_62])).
% 2.89/1.46  tff(c_80, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_71, c_45])).
% 2.89/1.46  tff(c_297, plain, (![B_47, C_48, A_49]: (r1_tarski(u1_struct_0(B_47), u1_struct_0(C_48)) | ~m1_pre_topc(B_47, C_48) | ~m1_pre_topc(C_48, A_49) | ~m1_pre_topc(B_47, A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.89/1.46  tff(c_301, plain, (![B_47]: (r1_tarski(u1_struct_0(B_47), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_47, '#skF_3') | ~m1_pre_topc(B_47, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_297])).
% 2.89/1.46  tff(c_387, plain, (![B_54]: (r1_tarski(u1_struct_0(B_54), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_80, c_301])).
% 2.89/1.46  tff(c_393, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_387])).
% 2.89/1.46  tff(c_400, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_393])).
% 2.89/1.46  tff(c_104, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_95])).
% 2.89/1.46  tff(c_130, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_104])).
% 2.89/1.46  tff(c_133, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_130])).
% 2.89/1.46  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_133])).
% 2.89/1.46  tff(c_139, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_104])).
% 2.89/1.46  tff(c_170, plain, (![A_37, B_38]: (r1_xboole_0(u1_struct_0(A_37), u1_struct_0(B_38)) | ~r1_tsep_1(A_37, B_38) | ~l1_struct_0(B_38) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.46  tff(c_185, plain, (![B_38]: (r1_xboole_0(k2_struct_0('#skF_2'), u1_struct_0(B_38)) | ~r1_tsep_1('#skF_2', B_38) | ~l1_struct_0(B_38) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_170])).
% 2.89/1.46  tff(c_402, plain, (![B_55]: (r1_xboole_0(k2_struct_0('#skF_2'), u1_struct_0(B_55)) | ~r1_tsep_1('#skF_2', B_55) | ~l1_struct_0(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_185])).
% 2.89/1.46  tff(c_408, plain, (r1_xboole_0(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_80, c_402])).
% 2.89/1.46  tff(c_417, plain, (r1_xboole_0(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_40, c_408])).
% 2.89/1.46  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.46  tff(c_426, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_417, c_2])).
% 2.89/1.46  tff(c_429, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_426])).
% 2.89/1.46  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k2_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.89/1.46  tff(c_432, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_429, c_10])).
% 2.89/1.46  tff(c_435, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_432])).
% 2.89/1.46  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_435])).
% 2.89/1.46  tff(c_439, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.89/1.46  tff(c_438, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.89/1.46  tff(c_491, plain, (![B_63, A_64]: (r1_tsep_1(B_63, A_64) | ~r1_tsep_1(A_64, B_63) | ~l1_struct_0(B_63) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.89/1.46  tff(c_493, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_438, c_491])).
% 2.89/1.46  tff(c_496, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_439, c_493])).
% 2.89/1.46  tff(c_497, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_496])).
% 2.89/1.46  tff(c_500, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_497])).
% 2.89/1.46  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_470, c_500])).
% 2.89/1.46  tff(c_505, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_496])).
% 2.89/1.46  tff(c_532, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_505])).
% 2.89/1.46  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_467, c_532])).
% 2.89/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  Inference rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Ref     : 0
% 2.89/1.46  #Sup     : 105
% 2.89/1.46  #Fact    : 0
% 2.89/1.46  #Define  : 0
% 2.89/1.46  #Split   : 16
% 2.89/1.46  #Chain   : 0
% 2.89/1.46  #Close   : 0
% 2.89/1.46  
% 2.89/1.46  Ordering : KBO
% 2.89/1.46  
% 2.89/1.46  Simplification rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Subsume      : 1
% 2.89/1.46  #Demod        : 70
% 2.89/1.46  #Tautology    : 23
% 2.89/1.46  #SimpNegUnit  : 7
% 2.89/1.46  #BackRed      : 0
% 2.89/1.46  
% 2.89/1.46  #Partial instantiations: 0
% 2.89/1.46  #Strategies tried      : 1
% 2.89/1.46  
% 2.89/1.46  Timing (in seconds)
% 2.89/1.46  ----------------------
% 3.07/1.47  Preprocessing        : 0.31
% 3.07/1.47  Parsing              : 0.17
% 3.07/1.47  CNF conversion       : 0.02
% 3.07/1.47  Main loop            : 0.38
% 3.07/1.47  Inferencing          : 0.14
% 3.07/1.47  Reduction            : 0.12
% 3.07/1.47  Demodulation         : 0.08
% 3.07/1.47  BG Simplification    : 0.02
% 3.07/1.47  Subsumption          : 0.07
% 3.07/1.47  Abstraction          : 0.02
% 3.07/1.47  MUC search           : 0.00
% 3.07/1.47  Cooper               : 0.00
% 3.07/1.47  Total                : 0.74
% 3.07/1.47  Index Insertion      : 0.00
% 3.07/1.47  Index Deletion       : 0.00
% 3.07/1.47  Index Matching       : 0.00
% 3.07/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
