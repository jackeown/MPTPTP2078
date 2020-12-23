%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 281 expanded)
%              Number of leaves         :   40 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 772 expanded)
%              Number of equality atoms :   16 ( 102 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v2_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_2] : r1_tarski('#skF_5',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_36] :
      ( v4_pre_topc(k2_struct_0(A_36),A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_92,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_96,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_118,plain,(
    ! [A_69] :
      ( m1_subset_1('#skF_2'(A_69),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_121,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_118])).

tff(c_123,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_322,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ v1_xboole_0(C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_331,plain,(
    ! [A_97] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_97,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_123,c_322])).

tff(c_356,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_98,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_37] :
      ( v3_pre_topc(k2_struct_0(A_37),A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_50,plain,(
    ! [D_52] :
      ( v4_pre_topc(D_52,'#skF_3')
      | ~ r2_hidden(D_52,'#skF_5')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_104,plain,(
    ! [D_66] :
      ( v4_pre_topc(D_66,'#skF_3')
      | ~ r2_hidden(D_66,'#skF_5')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_50])).

tff(c_109,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_104])).

tff(c_316,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_46,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,'#skF_5')
      | ~ r2_hidden('#skF_4',D_52)
      | ~ v4_pre_topc(D_52,'#skF_3')
      | ~ v3_pre_topc(D_52,'#skF_3')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_393,plain,(
    ! [D_106] :
      ( r2_hidden(D_106,'#skF_5')
      | ~ r2_hidden('#skF_4',D_106)
      | ~ v4_pre_topc(D_106,'#skF_3')
      | ~ v3_pre_topc(D_106,'#skF_3')
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_46])).

tff(c_400,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_393])).

tff(c_406,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_400])).

tff(c_408,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_411,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_411])).

tff(c_416,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_418,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_430,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_418])).

tff(c_433,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_430])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_433])).

tff(c_436,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_448,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_436])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_448])).

tff(c_454,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_469,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_454,c_57])).

tff(c_509,plain,(
    ! [A_116] :
      ( ~ v2_tops_1(k2_struct_0(A_116),A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_512,plain,
    ( ~ v2_tops_1('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_509])).

tff(c_514,plain,
    ( ~ v2_tops_1('#skF_5','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_512])).

tff(c_515,plain,(
    ~ v2_tops_1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_514])).

tff(c_18,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | A_12 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_526,plain,(
    ! [A_118] : ~ r2_hidden(A_118,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_536,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_526])).

tff(c_28,plain,(
    ! [A_38] :
      ( v2_tops_1('#skF_2'(A_38),A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_544,plain,
    ( v2_tops_1('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_28])).

tff(c_550,plain,(
    v2_tops_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_544])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_550])).

tff(c_554,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_557,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_554,c_14])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.35  % Computer   : n024.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:55:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.71/1.40  
% 2.71/1.40  %Foreground sorts:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Background operators:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Foreground operators:
% 2.71/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.40  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.71/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.71/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.71/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.71/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.40  
% 2.71/1.42  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.71/1.42  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.42  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.71/1.42  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.71/1.42  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.71/1.42  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v2_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 2.71/1.42  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.71/1.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.71/1.42  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.71/1.42  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.71/1.42  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.71/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.71/1.42  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_tops_1)).
% 2.71/1.42  tff(f_74, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.71/1.42  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.71/1.42  tff(c_34, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.42  tff(c_56, plain, (![A_2]: (r1_tarski('#skF_5', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 2.71/1.42  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_24, plain, (![A_36]: (v4_pre_topc(k2_struct_0(A_36), A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.42  tff(c_22, plain, (![A_35]: (l1_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.42  tff(c_76, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.42  tff(c_92, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_22, c_76])).
% 2.71/1.42  tff(c_96, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_92])).
% 2.71/1.42  tff(c_118, plain, (![A_69]: (m1_subset_1('#skF_2'(A_69), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.71/1.42  tff(c_121, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_96, c_118])).
% 2.71/1.42  tff(c_123, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_121])).
% 2.71/1.42  tff(c_322, plain, (![C_95, B_96, A_97]: (~v1_xboole_0(C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.42  tff(c_331, plain, (![A_97]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_97, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_123, c_322])).
% 2.71/1.42  tff(c_356, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_331])).
% 2.71/1.42  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_98, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_38])).
% 2.71/1.42  tff(c_10, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.42  tff(c_26, plain, (![A_37]: (v3_pre_topc(k2_struct_0(A_37), A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.71/1.42  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.42  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.42  tff(c_55, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.71/1.42  tff(c_50, plain, (![D_52]: (v4_pre_topc(D_52, '#skF_3') | ~r2_hidden(D_52, '#skF_5') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_104, plain, (![D_66]: (v4_pre_topc(D_66, '#skF_3') | ~r2_hidden(D_66, '#skF_5') | ~m1_subset_1(D_66, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_50])).
% 2.71/1.42  tff(c_109, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_55, c_104])).
% 2.71/1.42  tff(c_316, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_109])).
% 2.71/1.42  tff(c_46, plain, (![D_52]: (r2_hidden(D_52, '#skF_5') | ~r2_hidden('#skF_4', D_52) | ~v4_pre_topc(D_52, '#skF_3') | ~v3_pre_topc(D_52, '#skF_3') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.71/1.42  tff(c_393, plain, (![D_106]: (r2_hidden(D_106, '#skF_5') | ~r2_hidden('#skF_4', D_106) | ~v4_pre_topc(D_106, '#skF_3') | ~v3_pre_topc(D_106, '#skF_3') | ~m1_subset_1(D_106, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_46])).
% 2.71/1.42  tff(c_400, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_393])).
% 2.71/1.42  tff(c_406, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_316, c_400])).
% 2.71/1.42  tff(c_408, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_406])).
% 2.71/1.42  tff(c_411, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_408])).
% 2.71/1.42  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_411])).
% 2.71/1.42  tff(c_416, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_406])).
% 2.71/1.42  tff(c_418, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_416])).
% 2.71/1.42  tff(c_430, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_418])).
% 2.71/1.42  tff(c_433, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_430])).
% 2.71/1.42  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_433])).
% 2.71/1.42  tff(c_436, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_416])).
% 2.71/1.42  tff(c_448, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_436])).
% 2.71/1.42  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_448])).
% 2.71/1.42  tff(c_454, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_331])).
% 2.71/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.42  tff(c_57, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 2.71/1.42  tff(c_469, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_454, c_57])).
% 2.71/1.42  tff(c_509, plain, (![A_116]: (~v2_tops_1(k2_struct_0(A_116), A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.71/1.42  tff(c_512, plain, (~v2_tops_1('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_469, c_509])).
% 2.71/1.42  tff(c_514, plain, (~v2_tops_1('#skF_5', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_512])).
% 2.71/1.42  tff(c_515, plain, (~v2_tops_1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_514])).
% 2.71/1.42  tff(c_18, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.42  tff(c_53, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | A_12='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 2.71/1.42  tff(c_526, plain, (![A_118]: (~r2_hidden(A_118, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_331])).
% 2.71/1.42  tff(c_536, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_53, c_526])).
% 2.71/1.42  tff(c_28, plain, (![A_38]: (v2_tops_1('#skF_2'(A_38), A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.71/1.42  tff(c_544, plain, (v2_tops_1('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_536, c_28])).
% 2.71/1.42  tff(c_550, plain, (v2_tops_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_544])).
% 2.71/1.42  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_550])).
% 2.71/1.42  tff(c_554, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_109])).
% 2.71/1.42  tff(c_14, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.42  tff(c_557, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_554, c_14])).
% 2.71/1.42  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_557])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 88
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 14
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 17
% 2.71/1.42  #Demod        : 69
% 2.71/1.42  #Tautology    : 20
% 2.71/1.42  #SimpNegUnit  : 10
% 2.71/1.42  #BackRed      : 23
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.42  Preprocessing        : 0.34
% 2.71/1.42  Parsing              : 0.19
% 2.71/1.42  CNF conversion       : 0.03
% 2.71/1.42  Main loop            : 0.30
% 2.71/1.42  Inferencing          : 0.11
% 2.71/1.42  Reduction            : 0.09
% 2.71/1.42  Demodulation         : 0.06
% 2.71/1.42  BG Simplification    : 0.02
% 2.71/1.42  Subsumption          : 0.05
% 2.71/1.42  Abstraction          : 0.01
% 2.71/1.42  MUC search           : 0.00
% 2.71/1.42  Cooper               : 0.00
% 2.71/1.42  Total                : 0.68
% 2.71/1.42  Index Insertion      : 0.00
% 2.71/1.42  Index Deletion       : 0.00
% 2.71/1.42  Index Matching       : 0.00
% 2.71/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
