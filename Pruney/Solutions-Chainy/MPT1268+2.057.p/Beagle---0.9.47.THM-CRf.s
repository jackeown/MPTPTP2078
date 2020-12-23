%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 396 expanded)
%              Number of leaves         :   30 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  335 (1247 expanded)
%              Number of equality atoms :   57 ( 160 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_62,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_126,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tops_1(A_82,B_83),B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_135,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_131])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_665,plain,(
    ! [A_134,B_135] :
      ( v3_pre_topc(k1_tops_1(A_134,B_135),A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_670,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_665])).

tff(c_674,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_670])).

tff(c_76,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_86,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_86])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_500,plain,(
    ! [A_119,B_120] :
      ( v3_pre_topc(k1_tops_1(A_119,B_120),A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_505,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_500])).

tff(c_509,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_505])).

tff(c_52,plain,(
    ! [C_50] :
      ( k1_xboole_0 != '#skF_5'
      | k1_xboole_0 = C_50
      | ~ v3_pre_topc(C_50,'#skF_3')
      | ~ r1_tarski(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_115,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    ! [C_50] :
      ( r1_tarski('#skF_5','#skF_4')
      | k1_xboole_0 = C_50
      | ~ v3_pre_topc(C_50,'#skF_3')
      | ~ r1_tarski(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_150,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [C_50] :
      ( v3_pre_topc('#skF_5','#skF_3')
      | k1_xboole_0 = C_50
      | ~ v3_pre_topc(C_50,'#skF_3')
      | ~ r1_tarski(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_244,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    ! [C_50] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_50
      | ~ v3_pre_topc(C_50,'#skF_3')
      | ~ r1_tarski(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_350,plain,(
    ! [C_105] :
      ( k1_xboole_0 = C_105
      | ~ v3_pre_topc(C_105,'#skF_3')
      | ~ r1_tarski(C_105,'#skF_4')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60])).

tff(c_369,plain,(
    ! [A_107] :
      ( k1_xboole_0 = A_107
      | ~ v3_pre_topc(A_107,'#skF_3')
      | ~ r1_tarski(A_107,'#skF_4')
      | ~ r1_tarski(A_107,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_350])).

tff(c_396,plain,(
    ! [A_108] :
      ( k1_xboole_0 = A_108
      | ~ v3_pre_topc(A_108,'#skF_3')
      | ~ r1_tarski(A_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_369])).

tff(c_399,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_396])).

tff(c_402,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_399])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_402])).

tff(c_425,plain,(
    ! [C_112] :
      ( k1_xboole_0 = C_112
      | ~ v3_pre_topc(C_112,'#skF_3')
      | ~ r1_tarski(C_112,'#skF_4')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_442,plain,(
    ! [A_114] :
      ( k1_xboole_0 = A_114
      | ~ v3_pre_topc(A_114,'#skF_3')
      | ~ r1_tarski(A_114,'#skF_4')
      | ~ r1_tarski(A_114,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_425])).

tff(c_463,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v3_pre_topc(A_60,'#skF_3')
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_442])).

tff(c_512,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_509,c_463])).

tff(c_515,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_512])).

tff(c_529,plain,(
    ! [B_121,A_122] :
      ( v2_tops_1(B_121,A_122)
      | k1_tops_1(A_122,B_121) != k1_xboole_0
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_536,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_529])).

tff(c_540,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_515,c_536])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_540])).

tff(c_622,plain,(
    ! [C_131] :
      ( k1_xboole_0 = C_131
      | ~ v3_pre_topc(C_131,'#skF_3')
      | ~ r1_tarski(C_131,'#skF_4')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_632,plain,(
    ! [A_132] :
      ( k1_xboole_0 = A_132
      | ~ v3_pre_topc(A_132,'#skF_3')
      | ~ r1_tarski(A_132,'#skF_4')
      | ~ r1_tarski(A_132,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_622])).

tff(c_653,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v3_pre_topc(A_60,'#skF_3')
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_632])).

tff(c_678,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_674,c_653])).

tff(c_681,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_678])).

tff(c_745,plain,(
    ! [B_139,A_140] :
      ( v2_tops_1(B_139,A_140)
      | k1_tops_1(A_140,B_139) != k1_xboole_0
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_752,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_745])).

tff(c_756,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_681,c_752])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_756])).

tff(c_760,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_32,plain,(
    ! [B_42,A_40] :
      ( v2_tops_1(B_42,A_40)
      | k1_tops_1(A_40,B_42) != k1_xboole_0
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_964,plain,(
    ! [B_176,A_177] :
      ( v2_tops_1(B_176,A_177)
      | k1_tops_1(A_177,B_176) != '#skF_5'
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_32])).

tff(c_971,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_964])).

tff(c_975,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_971])).

tff(c_976,plain,(
    k1_tops_1('#skF_3','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_975])).

tff(c_808,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(k1_tops_1(A_160,B_161),B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_813,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_808])).

tff(c_817,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_813])).

tff(c_1054,plain,(
    ! [A_185,B_186] :
      ( v3_pre_topc(k1_tops_1(A_185,B_186),A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1059,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1054])).

tff(c_1063,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1059])).

tff(c_818,plain,(
    ! [C_50] :
      ( v2_tops_1('#skF_4','#skF_3')
      | C_50 = '#skF_5'
      | ~ v3_pre_topc(C_50,'#skF_3')
      | ~ r1_tarski(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_60])).

tff(c_820,plain,(
    ! [C_162] :
      ( C_162 = '#skF_5'
      | ~ v3_pre_topc(C_162,'#skF_3')
      | ~ r1_tarski(C_162,'#skF_4')
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_818])).

tff(c_922,plain,(
    ! [A_172] :
      ( A_172 = '#skF_5'
      | ~ v3_pre_topc(A_172,'#skF_3')
      | ~ r1_tarski(A_172,'#skF_4')
      | ~ r1_tarski(A_172,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_820])).

tff(c_947,plain,(
    ! [A_60] :
      ( A_60 = '#skF_5'
      | ~ v3_pre_topc(A_60,'#skF_3')
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_922])).

tff(c_1066,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1063,c_947])).

tff(c_1069,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_1066])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_976,c_1069])).

tff(c_1072,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1073,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1078,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1076,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_46])).

tff(c_48,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1102,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_48])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1198,plain,(
    ! [A_221,B_222] :
      ( r1_tarski(k1_tops_1(A_221,B_222),B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1337,plain,(
    ! [A_231,A_232] :
      ( r1_tarski(k1_tops_1(A_231,A_232),A_232)
      | ~ l1_pre_topc(A_231)
      | ~ r1_tarski(A_232,u1_struct_0(A_231)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1198])).

tff(c_1107,plain,(
    ! [A_195,C_196,B_197] :
      ( r1_tarski(A_195,C_196)
      | ~ r1_tarski(B_197,C_196)
      | ~ r1_tarski(A_195,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1119,plain,(
    ! [A_195,A_4] :
      ( r1_tarski(A_195,A_4)
      | ~ r1_tarski(A_195,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_1107])).

tff(c_1356,plain,(
    ! [A_231,A_4] :
      ( r1_tarski(k1_tops_1(A_231,k1_xboole_0),A_4)
      | ~ l1_pre_topc(A_231)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_231)) ) ),
    inference(resolution,[status(thm)],[c_1337,c_1119])).

tff(c_1378,plain,(
    ! [A_233,A_234] :
      ( r1_tarski(k1_tops_1(A_233,k1_xboole_0),A_234)
      | ~ l1_pre_topc(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1356])).

tff(c_1079,plain,(
    ! [A_189] :
      ( r2_hidden('#skF_1'(A_189),A_189)
      | k1_xboole_0 = A_189 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1083,plain,(
    ! [A_189] :
      ( ~ r1_tarski(A_189,'#skF_1'(A_189))
      | k1_xboole_0 = A_189 ) ),
    inference(resolution,[status(thm)],[c_1079,c_10])).

tff(c_1432,plain,(
    ! [A_237] :
      ( k1_tops_1(A_237,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_1378,c_1083])).

tff(c_1436,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_1432])).

tff(c_1533,plain,(
    ! [B_245,A_246,C_247] :
      ( r2_hidden(B_245,'#skF_2'(A_246,B_245,C_247))
      | ~ r2_hidden(B_245,k1_tops_1(A_246,C_247))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1535,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,'#skF_2'('#skF_3',B_245,k1_xboole_0))
      | ~ r2_hidden(B_245,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_1533])).

tff(c_1542,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,'#skF_2'('#skF_3',B_245,k1_xboole_0))
      | ~ r2_hidden(B_245,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1535])).

tff(c_1609,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_1612,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_1609])).

tff(c_1616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1612])).

tff(c_1618,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_1577,plain,(
    ! [A_251,B_252,C_253] :
      ( r1_tarski('#skF_2'(A_251,B_252,C_253),C_253)
      | ~ r2_hidden(B_252,k1_tops_1(A_251,C_253))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1579,plain,(
    ! [B_252] :
      ( r1_tarski('#skF_2'('#skF_3',B_252,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_252,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_1577])).

tff(c_1586,plain,(
    ! [B_252] :
      ( r1_tarski('#skF_2'('#skF_3',B_252,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_252,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1579])).

tff(c_1705,plain,(
    ! [B_263] :
      ( r1_tarski('#skF_2'('#skF_3',B_263,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_263,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1586])).

tff(c_1727,plain,(
    ! [B_264,A_265] :
      ( r1_tarski('#skF_2'('#skF_3',B_264,k1_xboole_0),A_265)
      | ~ r2_hidden(B_264,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1705,c_1119])).

tff(c_1658,plain,(
    ! [B_255] :
      ( r2_hidden(B_255,'#skF_2'('#skF_3',B_255,k1_xboole_0))
      | ~ r2_hidden(B_255,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_1668,plain,(
    ! [B_255] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_255,k1_xboole_0),B_255)
      | ~ r2_hidden(B_255,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1658,c_10])).

tff(c_1768,plain,(
    ! [A_265] : ~ r2_hidden(A_265,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1727,c_1668])).

tff(c_1300,plain,(
    ! [A_228,B_229] :
      ( k1_tops_1(A_228,B_229) = k1_xboole_0
      | ~ v2_tops_1(B_229,A_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1310,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1300])).

tff(c_1318,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1073,c_1310])).

tff(c_12,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1883,plain,(
    ! [B_275,A_276,C_277,D_278] :
      ( r2_hidden(B_275,k1_tops_1(A_276,C_277))
      | ~ r2_hidden(B_275,D_278)
      | ~ r1_tarski(D_278,C_277)
      | ~ v3_pre_topc(D_278,A_276)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ m1_subset_1(C_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4351,plain,(
    ! [A_412,A_413,C_414] :
      ( r2_hidden('#skF_1'(A_412),k1_tops_1(A_413,C_414))
      | ~ r1_tarski(A_412,C_414)
      | ~ v3_pre_topc(A_412,A_413)
      | ~ m1_subset_1(A_412,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | k1_xboole_0 = A_412 ) ),
    inference(resolution,[status(thm)],[c_12,c_1883])).

tff(c_4388,plain,(
    ! [A_412] :
      ( r2_hidden('#skF_1'(A_412),k1_xboole_0)
      | ~ r1_tarski(A_412,'#skF_4')
      | ~ v3_pre_topc(A_412,'#skF_3')
      | ~ m1_subset_1(A_412,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | k1_xboole_0 = A_412 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1318,c_4351])).

tff(c_4415,plain,(
    ! [A_412] :
      ( r2_hidden('#skF_1'(A_412),k1_xboole_0)
      | ~ r1_tarski(A_412,'#skF_4')
      | ~ v3_pre_topc(A_412,'#skF_3')
      | ~ m1_subset_1(A_412,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_412 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_4388])).

tff(c_4417,plain,(
    ! [A_415] :
      ( ~ r1_tarski(A_415,'#skF_4')
      | ~ v3_pre_topc(A_415,'#skF_3')
      | ~ m1_subset_1(A_415,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_415 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1768,c_4415])).

tff(c_4427,plain,
    ( ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1102,c_4417])).

tff(c_4444,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1076,c_4427])).

tff(c_4446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1072,c_4444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.08  
% 5.33/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.08  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_mcart_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.70/2.08  
% 5.70/2.08  %Foreground sorts:
% 5.70/2.08  
% 5.70/2.08  
% 5.70/2.08  %Background operators:
% 5.70/2.08  
% 5.70/2.08  
% 5.70/2.08  %Foreground operators:
% 5.70/2.08  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.70/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.70/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.70/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.08  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.70/2.08  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.70/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.70/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.70/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.70/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.70/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.70/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.70/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.70/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.70/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.08  
% 5.79/2.10  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 5.79/2.10  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.79/2.10  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.79/2.10  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.79/2.10  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.79/2.10  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.79/2.10  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.79/2.10  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.79/2.10  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.79/2.10  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 5.79/2.11  tff(c_42, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_62, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 5.79/2.11  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_126, plain, (![A_82, B_83]: (r1_tarski(k1_tops_1(A_82, B_83), B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.79/2.11  tff(c_131, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_126])).
% 5.79/2.11  tff(c_135, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_131])).
% 5.79/2.11  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_665, plain, (![A_134, B_135]: (v3_pre_topc(k1_tops_1(A_134, B_135), A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.11  tff(c_670, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_665])).
% 5.79/2.11  tff(c_674, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_670])).
% 5.79/2.11  tff(c_76, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.11  tff(c_80, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_76])).
% 5.79/2.11  tff(c_86, plain, (![A_60, C_61, B_62]: (r1_tarski(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.79/2.11  tff(c_91, plain, (![A_60]: (r1_tarski(A_60, u1_struct_0('#skF_3')) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_86])).
% 5.79/2.11  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.11  tff(c_500, plain, (![A_119, B_120]: (v3_pre_topc(k1_tops_1(A_119, B_120), A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.11  tff(c_505, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_500])).
% 5.79/2.11  tff(c_509, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_505])).
% 5.79/2.11  tff(c_52, plain, (![C_50]: (k1_xboole_0!='#skF_5' | k1_xboole_0=C_50 | ~v3_pre_topc(C_50, '#skF_3') | ~r1_tarski(C_50, '#skF_4') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_115, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_52])).
% 5.79/2.11  tff(c_56, plain, (![C_50]: (r1_tarski('#skF_5', '#skF_4') | k1_xboole_0=C_50 | ~v3_pre_topc(C_50, '#skF_3') | ~r1_tarski(C_50, '#skF_4') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_150, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 5.79/2.11  tff(c_54, plain, (![C_50]: (v3_pre_topc('#skF_5', '#skF_3') | k1_xboole_0=C_50 | ~v3_pre_topc(C_50, '#skF_3') | ~r1_tarski(C_50, '#skF_4') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_244, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 5.79/2.11  tff(c_60, plain, (![C_50]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_50 | ~v3_pre_topc(C_50, '#skF_3') | ~r1_tarski(C_50, '#skF_4') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_350, plain, (![C_105]: (k1_xboole_0=C_105 | ~v3_pre_topc(C_105, '#skF_3') | ~r1_tarski(C_105, '#skF_4') | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_60])).
% 5.79/2.11  tff(c_369, plain, (![A_107]: (k1_xboole_0=A_107 | ~v3_pre_topc(A_107, '#skF_3') | ~r1_tarski(A_107, '#skF_4') | ~r1_tarski(A_107, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_350])).
% 5.79/2.11  tff(c_396, plain, (![A_108]: (k1_xboole_0=A_108 | ~v3_pre_topc(A_108, '#skF_3') | ~r1_tarski(A_108, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_369])).
% 5.79/2.11  tff(c_399, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_244, c_396])).
% 5.79/2.11  tff(c_402, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_399])).
% 5.79/2.11  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_402])).
% 5.79/2.11  tff(c_425, plain, (![C_112]: (k1_xboole_0=C_112 | ~v3_pre_topc(C_112, '#skF_3') | ~r1_tarski(C_112, '#skF_4') | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_54])).
% 5.79/2.11  tff(c_442, plain, (![A_114]: (k1_xboole_0=A_114 | ~v3_pre_topc(A_114, '#skF_3') | ~r1_tarski(A_114, '#skF_4') | ~r1_tarski(A_114, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_425])).
% 5.79/2.11  tff(c_463, plain, (![A_60]: (k1_xboole_0=A_60 | ~v3_pre_topc(A_60, '#skF_3') | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_442])).
% 5.79/2.11  tff(c_512, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_509, c_463])).
% 5.79/2.11  tff(c_515, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_512])).
% 5.79/2.11  tff(c_529, plain, (![B_121, A_122]: (v2_tops_1(B_121, A_122) | k1_tops_1(A_122, B_121)!=k1_xboole_0 | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.79/2.11  tff(c_536, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_529])).
% 5.79/2.11  tff(c_540, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_515, c_536])).
% 5.79/2.11  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_540])).
% 5.79/2.11  tff(c_622, plain, (![C_131]: (k1_xboole_0=C_131 | ~v3_pre_topc(C_131, '#skF_3') | ~r1_tarski(C_131, '#skF_4') | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_56])).
% 5.79/2.11  tff(c_632, plain, (![A_132]: (k1_xboole_0=A_132 | ~v3_pre_topc(A_132, '#skF_3') | ~r1_tarski(A_132, '#skF_4') | ~r1_tarski(A_132, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_622])).
% 5.79/2.11  tff(c_653, plain, (![A_60]: (k1_xboole_0=A_60 | ~v3_pre_topc(A_60, '#skF_3') | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_632])).
% 5.79/2.11  tff(c_678, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_674, c_653])).
% 5.79/2.11  tff(c_681, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_678])).
% 5.79/2.11  tff(c_745, plain, (![B_139, A_140]: (v2_tops_1(B_139, A_140) | k1_tops_1(A_140, B_139)!=k1_xboole_0 | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.79/2.11  tff(c_752, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_745])).
% 5.79/2.11  tff(c_756, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_681, c_752])).
% 5.79/2.11  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_756])).
% 5.79/2.11  tff(c_760, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 5.79/2.11  tff(c_32, plain, (![B_42, A_40]: (v2_tops_1(B_42, A_40) | k1_tops_1(A_40, B_42)!=k1_xboole_0 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.79/2.11  tff(c_964, plain, (![B_176, A_177]: (v2_tops_1(B_176, A_177) | k1_tops_1(A_177, B_176)!='#skF_5' | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_32])).
% 5.79/2.11  tff(c_971, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_964])).
% 5.79/2.11  tff(c_975, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_971])).
% 5.79/2.11  tff(c_976, plain, (k1_tops_1('#skF_3', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_975])).
% 5.79/2.11  tff(c_808, plain, (![A_160, B_161]: (r1_tarski(k1_tops_1(A_160, B_161), B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.79/2.11  tff(c_813, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_808])).
% 5.79/2.11  tff(c_817, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_813])).
% 5.79/2.11  tff(c_1054, plain, (![A_185, B_186]: (v3_pre_topc(k1_tops_1(A_185, B_186), A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.11  tff(c_1059, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1054])).
% 5.79/2.11  tff(c_1063, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1059])).
% 5.79/2.11  tff(c_818, plain, (![C_50]: (v2_tops_1('#skF_4', '#skF_3') | C_50='#skF_5' | ~v3_pre_topc(C_50, '#skF_3') | ~r1_tarski(C_50, '#skF_4') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_60])).
% 5.79/2.11  tff(c_820, plain, (![C_162]: (C_162='#skF_5' | ~v3_pre_topc(C_162, '#skF_3') | ~r1_tarski(C_162, '#skF_4') | ~m1_subset_1(C_162, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_818])).
% 5.79/2.11  tff(c_922, plain, (![A_172]: (A_172='#skF_5' | ~v3_pre_topc(A_172, '#skF_3') | ~r1_tarski(A_172, '#skF_4') | ~r1_tarski(A_172, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_820])).
% 5.79/2.11  tff(c_947, plain, (![A_60]: (A_60='#skF_5' | ~v3_pre_topc(A_60, '#skF_3') | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_922])).
% 5.79/2.11  tff(c_1066, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1063, c_947])).
% 5.79/2.11  tff(c_1069, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_1066])).
% 5.79/2.11  tff(c_1071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_976, c_1069])).
% 5.79/2.11  tff(c_1072, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 5.79/2.11  tff(c_1073, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 5.79/2.11  tff(c_44, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_1078, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_44])).
% 5.79/2.11  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_1076, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_46])).
% 5.79/2.11  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.79/2.11  tff(c_1102, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_48])).
% 5.79/2.11  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.11  tff(c_1198, plain, (![A_221, B_222]: (r1_tarski(k1_tops_1(A_221, B_222), B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.79/2.11  tff(c_1337, plain, (![A_231, A_232]: (r1_tarski(k1_tops_1(A_231, A_232), A_232) | ~l1_pre_topc(A_231) | ~r1_tarski(A_232, u1_struct_0(A_231)))), inference(resolution, [status(thm)], [c_8, c_1198])).
% 5.79/2.11  tff(c_1107, plain, (![A_195, C_196, B_197]: (r1_tarski(A_195, C_196) | ~r1_tarski(B_197, C_196) | ~r1_tarski(A_195, B_197))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.79/2.11  tff(c_1119, plain, (![A_195, A_4]: (r1_tarski(A_195, A_4) | ~r1_tarski(A_195, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_1107])).
% 5.79/2.11  tff(c_1356, plain, (![A_231, A_4]: (r1_tarski(k1_tops_1(A_231, k1_xboole_0), A_4) | ~l1_pre_topc(A_231) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_231)))), inference(resolution, [status(thm)], [c_1337, c_1119])).
% 5.79/2.11  tff(c_1378, plain, (![A_233, A_234]: (r1_tarski(k1_tops_1(A_233, k1_xboole_0), A_234) | ~l1_pre_topc(A_233))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1356])).
% 5.79/2.11  tff(c_1079, plain, (![A_189]: (r2_hidden('#skF_1'(A_189), A_189) | k1_xboole_0=A_189)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.79/2.11  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.79/2.11  tff(c_1083, plain, (![A_189]: (~r1_tarski(A_189, '#skF_1'(A_189)) | k1_xboole_0=A_189)), inference(resolution, [status(thm)], [c_1079, c_10])).
% 5.79/2.11  tff(c_1432, plain, (![A_237]: (k1_tops_1(A_237, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_1378, c_1083])).
% 5.79/2.11  tff(c_1436, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_1432])).
% 5.79/2.11  tff(c_1533, plain, (![B_245, A_246, C_247]: (r2_hidden(B_245, '#skF_2'(A_246, B_245, C_247)) | ~r2_hidden(B_245, k1_tops_1(A_246, C_247)) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.79/2.11  tff(c_1535, plain, (![B_245]: (r2_hidden(B_245, '#skF_2'('#skF_3', B_245, k1_xboole_0)) | ~r2_hidden(B_245, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1436, c_1533])).
% 5.79/2.11  tff(c_1542, plain, (![B_245]: (r2_hidden(B_245, '#skF_2'('#skF_3', B_245, k1_xboole_0)) | ~r2_hidden(B_245, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1535])).
% 5.79/2.11  tff(c_1609, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1542])).
% 5.79/2.11  tff(c_1612, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1609])).
% 5.79/2.11  tff(c_1616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1612])).
% 5.79/2.11  tff(c_1618, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1542])).
% 5.79/2.11  tff(c_1577, plain, (![A_251, B_252, C_253]: (r1_tarski('#skF_2'(A_251, B_252, C_253), C_253) | ~r2_hidden(B_252, k1_tops_1(A_251, C_253)) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.79/2.11  tff(c_1579, plain, (![B_252]: (r1_tarski('#skF_2'('#skF_3', B_252, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_252, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1436, c_1577])).
% 5.79/2.11  tff(c_1586, plain, (![B_252]: (r1_tarski('#skF_2'('#skF_3', B_252, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_252, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1579])).
% 5.79/2.11  tff(c_1705, plain, (![B_263]: (r1_tarski('#skF_2'('#skF_3', B_263, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_263, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1586])).
% 5.79/2.11  tff(c_1727, plain, (![B_264, A_265]: (r1_tarski('#skF_2'('#skF_3', B_264, k1_xboole_0), A_265) | ~r2_hidden(B_264, k1_xboole_0))), inference(resolution, [status(thm)], [c_1705, c_1119])).
% 5.79/2.11  tff(c_1658, plain, (![B_255]: (r2_hidden(B_255, '#skF_2'('#skF_3', B_255, k1_xboole_0)) | ~r2_hidden(B_255, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1542])).
% 5.79/2.11  tff(c_1668, plain, (![B_255]: (~r1_tarski('#skF_2'('#skF_3', B_255, k1_xboole_0), B_255) | ~r2_hidden(B_255, k1_xboole_0))), inference(resolution, [status(thm)], [c_1658, c_10])).
% 5.79/2.11  tff(c_1768, plain, (![A_265]: (~r2_hidden(A_265, k1_xboole_0))), inference(resolution, [status(thm)], [c_1727, c_1668])).
% 5.79/2.11  tff(c_1300, plain, (![A_228, B_229]: (k1_tops_1(A_228, B_229)=k1_xboole_0 | ~v2_tops_1(B_229, A_228) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.79/2.11  tff(c_1310, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1300])).
% 5.79/2.11  tff(c_1318, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1073, c_1310])).
% 5.79/2.11  tff(c_12, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.79/2.11  tff(c_1883, plain, (![B_275, A_276, C_277, D_278]: (r2_hidden(B_275, k1_tops_1(A_276, C_277)) | ~r2_hidden(B_275, D_278) | ~r1_tarski(D_278, C_277) | ~v3_pre_topc(D_278, A_276) | ~m1_subset_1(D_278, k1_zfmisc_1(u1_struct_0(A_276))) | ~m1_subset_1(C_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.79/2.11  tff(c_4351, plain, (![A_412, A_413, C_414]: (r2_hidden('#skF_1'(A_412), k1_tops_1(A_413, C_414)) | ~r1_tarski(A_412, C_414) | ~v3_pre_topc(A_412, A_413) | ~m1_subset_1(A_412, k1_zfmisc_1(u1_struct_0(A_413))) | ~m1_subset_1(C_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413) | k1_xboole_0=A_412)), inference(resolution, [status(thm)], [c_12, c_1883])).
% 5.79/2.11  tff(c_4388, plain, (![A_412]: (r2_hidden('#skF_1'(A_412), k1_xboole_0) | ~r1_tarski(A_412, '#skF_4') | ~v3_pre_topc(A_412, '#skF_3') | ~m1_subset_1(A_412, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | k1_xboole_0=A_412)), inference(superposition, [status(thm), theory('equality')], [c_1318, c_4351])).
% 5.79/2.11  tff(c_4415, plain, (![A_412]: (r2_hidden('#skF_1'(A_412), k1_xboole_0) | ~r1_tarski(A_412, '#skF_4') | ~v3_pre_topc(A_412, '#skF_3') | ~m1_subset_1(A_412, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_412)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_4388])).
% 5.79/2.11  tff(c_4417, plain, (![A_415]: (~r1_tarski(A_415, '#skF_4') | ~v3_pre_topc(A_415, '#skF_3') | ~m1_subset_1(A_415, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_415)), inference(negUnitSimplification, [status(thm)], [c_1768, c_4415])).
% 5.79/2.11  tff(c_4427, plain, (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1102, c_4417])).
% 5.79/2.11  tff(c_4444, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_1076, c_4427])).
% 5.79/2.11  tff(c_4446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1072, c_4444])).
% 5.79/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.11  
% 5.79/2.11  Inference rules
% 5.79/2.11  ----------------------
% 5.79/2.11  #Ref     : 0
% 5.79/2.11  #Sup     : 903
% 5.79/2.11  #Fact    : 0
% 5.79/2.11  #Define  : 0
% 5.79/2.11  #Split   : 14
% 5.79/2.11  #Chain   : 0
% 5.79/2.11  #Close   : 0
% 5.79/2.11  
% 5.79/2.11  Ordering : KBO
% 5.79/2.11  
% 5.79/2.11  Simplification rules
% 5.79/2.11  ----------------------
% 5.79/2.11  #Subsume      : 347
% 5.79/2.11  #Demod        : 910
% 5.79/2.11  #Tautology    : 280
% 5.79/2.11  #SimpNegUnit  : 27
% 5.79/2.11  #BackRed      : 12
% 5.79/2.11  
% 5.79/2.11  #Partial instantiations: 0
% 5.79/2.11  #Strategies tried      : 1
% 5.79/2.11  
% 5.79/2.11  Timing (in seconds)
% 5.79/2.11  ----------------------
% 5.79/2.11  Preprocessing        : 0.33
% 5.79/2.11  Parsing              : 0.18
% 5.79/2.11  CNF conversion       : 0.02
% 5.79/2.11  Main loop            : 1.00
% 5.79/2.11  Inferencing          : 0.34
% 5.79/2.11  Reduction            : 0.33
% 5.79/2.11  Demodulation         : 0.23
% 5.79/2.11  BG Simplification    : 0.03
% 5.79/2.11  Subsumption          : 0.23
% 5.79/2.11  Abstraction          : 0.04
% 5.79/2.11  MUC search           : 0.00
% 5.79/2.11  Cooper               : 0.00
% 5.79/2.11  Total                : 1.37
% 5.79/2.11  Index Insertion      : 0.00
% 5.79/2.11  Index Deletion       : 0.00
% 5.79/2.11  Index Matching       : 0.00
% 5.79/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
