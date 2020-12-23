%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 258 expanded)
%              Number of leaves         :   29 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 ( 820 expanded)
%              Number of equality atoms :   55 ( 126 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1533,plain,(
    ! [A_147,B_148] :
      ( r1_tarski(k1_tops_1(A_147,B_148),B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1538,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1533])).

tff(c_1542,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1538])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1867,plain,(
    ! [A_172,B_173] :
      ( v3_pre_topc(k1_tops_1(A_172,B_173),A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1872,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1867])).

tff(c_1876,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1872])).

tff(c_158,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_158])).

tff(c_1485,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(A_143,C_144)
      | ~ r1_tarski(B_145,C_144)
      | ~ r1_tarski(A_143,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1490,plain,(
    ! [A_143] :
      ( r1_tarski(A_143,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_166,c_1485])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1173,plain,(
    ! [B_117,A_118] :
      ( v2_tops_1(B_117,A_118)
      | k1_tops_1(A_118,B_117) != k1_xboole_0
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1180,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1173])).

tff(c_1184,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1180])).

tff(c_1185,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1184])).

tff(c_189,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tops_1(A_54,B_55),B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_189])).

tff(c_198,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_194])).

tff(c_1394,plain,(
    ! [A_137,B_138] :
      ( v3_pre_topc(k1_tops_1(A_137,B_138),A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1399,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1394])).

tff(c_1403,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1399])).

tff(c_176,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(B_51,C_50)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_166,c_176])).

tff(c_982,plain,(
    ! [B_109,A_110] :
      ( v2_tops_1(B_109,A_110)
      | k1_tops_1(A_110,B_109) != k1_xboole_0
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_989,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_982])).

tff(c_993,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_989])).

tff(c_994,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_993])).

tff(c_264,plain,(
    ! [A_60,B_61] :
      ( v3_pre_topc(k1_tops_1(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_269,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_264])).

tff(c_273,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_269])).

tff(c_42,plain,(
    ! [C_35] :
      ( k1_xboole_0 != '#skF_3'
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_167,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,(
    ! [C_35] :
      ( r1_tarski('#skF_3','#skF_2')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_221,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [C_35] :
      ( v3_pre_topc('#skF_3','#skF_1')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_323,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    ! [C_35] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_387,plain,(
    ! [C_66] :
      ( k1_xboole_0 = C_66
      | ~ v3_pre_topc(C_66,'#skF_1')
      | ~ r1_tarski(C_66,'#skF_2')
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50])).

tff(c_676,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ v3_pre_topc(A_89,'#skF_1')
      | ~ r1_tarski(A_89,'#skF_2')
      | ~ r1_tarski(A_89,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_387])).

tff(c_703,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ v3_pre_topc(A_90,'#skF_1')
      | ~ r1_tarski(A_90,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_181,c_676])).

tff(c_706,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_323,c_703])).

tff(c_712,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_706])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_712])).

tff(c_720,plain,(
    ! [C_91] :
      ( k1_xboole_0 = C_91
      | ~ v3_pre_topc(C_91,'#skF_1')
      | ~ r1_tarski(C_91,'#skF_2')
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1009,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ v3_pre_topc(A_112,'#skF_1')
      | ~ r1_tarski(A_112,'#skF_2')
      | ~ r1_tarski(A_112,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_720])).

tff(c_1036,plain,(
    ! [A_113] :
      ( k1_xboole_0 = A_113
      | ~ v3_pre_topc(A_113,'#skF_1')
      | ~ r1_tarski(A_113,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_181,c_1009])).

tff(c_1039,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_273,c_1036])).

tff(c_1042,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1039])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_994,c_1042])).

tff(c_1112,plain,(
    ! [C_115] :
      ( k1_xboole_0 = C_115
      | ~ v3_pre_topc(C_115,'#skF_1')
      | ~ r1_tarski(C_115,'#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1404,plain,(
    ! [A_139] :
      ( k1_xboole_0 = A_139
      | ~ v3_pre_topc(A_139,'#skF_1')
      | ~ r1_tarski(A_139,'#skF_2')
      | ~ r1_tarski(A_139,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1112])).

tff(c_1431,plain,(
    ! [A_140] :
      ( k1_xboole_0 = A_140
      | ~ v3_pre_topc(A_140,'#skF_1')
      | ~ r1_tarski(A_140,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_181,c_1404])).

tff(c_1434,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1403,c_1431])).

tff(c_1437,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1434])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_1437])).

tff(c_1441,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1560,plain,(
    ! [C_35] :
      ( v2_tops_1('#skF_2','#skF_1')
      | C_35 = '#skF_3'
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_50])).

tff(c_1562,plain,(
    ! [C_151] :
      ( C_151 = '#skF_3'
      | ~ v3_pre_topc(C_151,'#skF_1')
      | ~ r1_tarski(C_151,'#skF_2')
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1560])).

tff(c_1754,plain,(
    ! [A_162] :
      ( A_162 = '#skF_3'
      | ~ v3_pre_topc(A_162,'#skF_1')
      | ~ r1_tarski(A_162,'#skF_2')
      | ~ r1_tarski(A_162,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1562])).

tff(c_1770,plain,(
    ! [A_143] :
      ( A_143 = '#skF_3'
      | ~ v3_pre_topc(A_143,'#skF_1')
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1490,c_1754])).

tff(c_1902,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1876,c_1770])).

tff(c_1905,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_1902])).

tff(c_22,plain,(
    ! [B_27,A_25] :
      ( v2_tops_1(B_27,A_25)
      | k1_tops_1(A_25,B_27) != k1_xboole_0
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1977,plain,(
    ! [B_176,A_177] :
      ( v2_tops_1(B_176,A_177)
      | k1_tops_1(A_177,B_176) != '#skF_3'
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_22])).

tff(c_1984,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1977])).

tff(c_1988,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1905,c_1984])).

tff(c_1990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1988])).

tff(c_1991,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1992,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2029,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_34])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1994,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_36])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2088,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_38])).

tff(c_2516,plain,(
    ! [A_210,B_211] :
      ( k1_tops_1(A_210,B_211) = k1_xboole_0
      | ~ v2_tops_1(B_211,A_210)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2526,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2516])).

tff(c_2534,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1992,c_2526])).

tff(c_2614,plain,(
    ! [B_213,A_214,C_215] :
      ( r1_tarski(B_213,k1_tops_1(A_214,C_215))
      | ~ r1_tarski(B_213,C_215)
      | ~ v3_pre_topc(B_213,A_214)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2621,plain,(
    ! [B_213] :
      ( r1_tarski(B_213,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_213,'#skF_2')
      | ~ v3_pre_topc(B_213,'#skF_1')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_2614])).

tff(c_2631,plain,(
    ! [B_216] :
      ( r1_tarski(B_216,k1_xboole_0)
      | ~ r1_tarski(B_216,'#skF_2')
      | ~ v3_pre_topc(B_216,'#skF_1')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2534,c_2621])).

tff(c_2634,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2088,c_2631])).

tff(c_2644,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_1994,c_2634])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2656,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2644,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2040,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(A_184,B_185) = A_184
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2062,plain,(
    ! [A_188] : k3_xboole_0(k1_xboole_0,A_188) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_2040])).

tff(c_2076,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2062])).

tff(c_2687,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_2076])).

tff(c_2693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1991,c_2687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:51:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.78  
% 3.86/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.78  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.86/1.78  
% 3.86/1.78  %Foreground sorts:
% 3.86/1.78  
% 3.86/1.78  
% 3.86/1.78  %Background operators:
% 3.86/1.78  
% 3.86/1.78  
% 3.86/1.78  %Foreground operators:
% 3.86/1.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.86/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.78  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.86/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.86/1.78  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.78  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.78  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.86/1.78  
% 4.24/1.80  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.24/1.80  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.24/1.80  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.24/1.80  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.24/1.80  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.24/1.80  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.24/1.80  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.24/1.80  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.24/1.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.24/1.80  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.24/1.80  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_52, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 4.24/1.80  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_1533, plain, (![A_147, B_148]: (r1_tarski(k1_tops_1(A_147, B_148), B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.24/1.80  tff(c_1538, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1533])).
% 4.24/1.80  tff(c_1542, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1538])).
% 4.24/1.80  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_1867, plain, (![A_172, B_173]: (v3_pre_topc(k1_tops_1(A_172, B_173), A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.24/1.80  tff(c_1872, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1867])).
% 4.24/1.80  tff(c_1876, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1872])).
% 4.24/1.80  tff(c_158, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.24/1.80  tff(c_166, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_158])).
% 4.24/1.80  tff(c_1485, plain, (![A_143, C_144, B_145]: (r1_tarski(A_143, C_144) | ~r1_tarski(B_145, C_144) | ~r1_tarski(A_143, B_145))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.24/1.80  tff(c_1490, plain, (![A_143]: (r1_tarski(A_143, u1_struct_0('#skF_1')) | ~r1_tarski(A_143, '#skF_2'))), inference(resolution, [status(thm)], [c_166, c_1485])).
% 4.24/1.80  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.24/1.80  tff(c_1173, plain, (![B_117, A_118]: (v2_tops_1(B_117, A_118) | k1_tops_1(A_118, B_117)!=k1_xboole_0 | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.80  tff(c_1180, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1173])).
% 4.24/1.80  tff(c_1184, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1180])).
% 4.24/1.80  tff(c_1185, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_1184])).
% 4.24/1.80  tff(c_189, plain, (![A_54, B_55]: (r1_tarski(k1_tops_1(A_54, B_55), B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.24/1.80  tff(c_194, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_189])).
% 4.24/1.80  tff(c_198, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_194])).
% 4.24/1.80  tff(c_1394, plain, (![A_137, B_138]: (v3_pre_topc(k1_tops_1(A_137, B_138), A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.24/1.80  tff(c_1399, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1394])).
% 4.24/1.80  tff(c_1403, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1399])).
% 4.24/1.80  tff(c_176, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(B_51, C_50) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.24/1.80  tff(c_181, plain, (![A_49]: (r1_tarski(A_49, u1_struct_0('#skF_1')) | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_166, c_176])).
% 4.24/1.80  tff(c_982, plain, (![B_109, A_110]: (v2_tops_1(B_109, A_110) | k1_tops_1(A_110, B_109)!=k1_xboole_0 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.80  tff(c_989, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_982])).
% 4.24/1.80  tff(c_993, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_989])).
% 4.24/1.80  tff(c_994, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_993])).
% 4.24/1.80  tff(c_264, plain, (![A_60, B_61]: (v3_pre_topc(k1_tops_1(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.24/1.80  tff(c_269, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_264])).
% 4.24/1.80  tff(c_273, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_269])).
% 4.24/1.80  tff(c_42, plain, (![C_35]: (k1_xboole_0!='#skF_3' | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_167, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_42])).
% 4.24/1.80  tff(c_46, plain, (![C_35]: (r1_tarski('#skF_3', '#skF_2') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_221, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.24/1.80  tff(c_44, plain, (![C_35]: (v3_pre_topc('#skF_3', '#skF_1') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_323, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.24/1.80  tff(c_50, plain, (![C_35]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_387, plain, (![C_66]: (k1_xboole_0=C_66 | ~v3_pre_topc(C_66, '#skF_1') | ~r1_tarski(C_66, '#skF_2') | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_50])).
% 4.24/1.80  tff(c_676, plain, (![A_89]: (k1_xboole_0=A_89 | ~v3_pre_topc(A_89, '#skF_1') | ~r1_tarski(A_89, '#skF_2') | ~r1_tarski(A_89, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_387])).
% 4.24/1.80  tff(c_703, plain, (![A_90]: (k1_xboole_0=A_90 | ~v3_pre_topc(A_90, '#skF_1') | ~r1_tarski(A_90, '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_676])).
% 4.24/1.80  tff(c_706, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_323, c_703])).
% 4.24/1.80  tff(c_712, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_706])).
% 4.24/1.80  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_712])).
% 4.24/1.80  tff(c_720, plain, (![C_91]: (k1_xboole_0=C_91 | ~v3_pre_topc(C_91, '#skF_1') | ~r1_tarski(C_91, '#skF_2') | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 4.24/1.80  tff(c_1009, plain, (![A_112]: (k1_xboole_0=A_112 | ~v3_pre_topc(A_112, '#skF_1') | ~r1_tarski(A_112, '#skF_2') | ~r1_tarski(A_112, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_720])).
% 4.24/1.80  tff(c_1036, plain, (![A_113]: (k1_xboole_0=A_113 | ~v3_pre_topc(A_113, '#skF_1') | ~r1_tarski(A_113, '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_1009])).
% 4.24/1.80  tff(c_1039, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_273, c_1036])).
% 4.24/1.80  tff(c_1042, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1039])).
% 4.24/1.80  tff(c_1044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_994, c_1042])).
% 4.24/1.80  tff(c_1112, plain, (![C_115]: (k1_xboole_0=C_115 | ~v3_pre_topc(C_115, '#skF_1') | ~r1_tarski(C_115, '#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.24/1.80  tff(c_1404, plain, (![A_139]: (k1_xboole_0=A_139 | ~v3_pre_topc(A_139, '#skF_1') | ~r1_tarski(A_139, '#skF_2') | ~r1_tarski(A_139, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1112])).
% 4.24/1.80  tff(c_1431, plain, (![A_140]: (k1_xboole_0=A_140 | ~v3_pre_topc(A_140, '#skF_1') | ~r1_tarski(A_140, '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_1404])).
% 4.24/1.80  tff(c_1434, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1403, c_1431])).
% 4.24/1.80  tff(c_1437, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1434])).
% 4.24/1.80  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1185, c_1437])).
% 4.24/1.80  tff(c_1441, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 4.24/1.80  tff(c_1560, plain, (![C_35]: (v2_tops_1('#skF_2', '#skF_1') | C_35='#skF_3' | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_50])).
% 4.24/1.80  tff(c_1562, plain, (![C_151]: (C_151='#skF_3' | ~v3_pre_topc(C_151, '#skF_1') | ~r1_tarski(C_151, '#skF_2') | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_1560])).
% 4.24/1.80  tff(c_1754, plain, (![A_162]: (A_162='#skF_3' | ~v3_pre_topc(A_162, '#skF_1') | ~r1_tarski(A_162, '#skF_2') | ~r1_tarski(A_162, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1562])).
% 4.24/1.80  tff(c_1770, plain, (![A_143]: (A_143='#skF_3' | ~v3_pre_topc(A_143, '#skF_1') | ~r1_tarski(A_143, '#skF_2'))), inference(resolution, [status(thm)], [c_1490, c_1754])).
% 4.24/1.80  tff(c_1902, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1876, c_1770])).
% 4.24/1.80  tff(c_1905, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_1902])).
% 4.24/1.80  tff(c_22, plain, (![B_27, A_25]: (v2_tops_1(B_27, A_25) | k1_tops_1(A_25, B_27)!=k1_xboole_0 | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.80  tff(c_1977, plain, (![B_176, A_177]: (v2_tops_1(B_176, A_177) | k1_tops_1(A_177, B_176)!='#skF_3' | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_22])).
% 4.24/1.80  tff(c_1984, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1977])).
% 4.24/1.80  tff(c_1988, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1905, c_1984])).
% 4.24/1.80  tff(c_1990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1988])).
% 4.24/1.80  tff(c_1991, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 4.24/1.80  tff(c_1992, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 4.24/1.80  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_2029, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1992, c_34])).
% 4.24/1.80  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_1994, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1992, c_36])).
% 4.24/1.80  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.24/1.80  tff(c_2088, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1992, c_38])).
% 4.24/1.80  tff(c_2516, plain, (![A_210, B_211]: (k1_tops_1(A_210, B_211)=k1_xboole_0 | ~v2_tops_1(B_211, A_210) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.80  tff(c_2526, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2516])).
% 4.24/1.80  tff(c_2534, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1992, c_2526])).
% 4.24/1.80  tff(c_2614, plain, (![B_213, A_214, C_215]: (r1_tarski(B_213, k1_tops_1(A_214, C_215)) | ~r1_tarski(B_213, C_215) | ~v3_pre_topc(B_213, A_214) | ~m1_subset_1(C_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.24/1.80  tff(c_2621, plain, (![B_213]: (r1_tarski(B_213, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_213, '#skF_2') | ~v3_pre_topc(B_213, '#skF_1') | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_2614])).
% 4.24/1.80  tff(c_2631, plain, (![B_216]: (r1_tarski(B_216, k1_xboole_0) | ~r1_tarski(B_216, '#skF_2') | ~v3_pre_topc(B_216, '#skF_1') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2534, c_2621])).
% 4.24/1.80  tff(c_2634, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2088, c_2631])).
% 4.24/1.80  tff(c_2644, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_1994, c_2634])).
% 4.24/1.80  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.24/1.80  tff(c_2656, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_2644, c_6])).
% 4.24/1.80  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.24/1.80  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.24/1.80  tff(c_2040, plain, (![A_184, B_185]: (k3_xboole_0(A_184, B_185)=A_184 | ~r1_tarski(A_184, B_185))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.24/1.80  tff(c_2062, plain, (![A_188]: (k3_xboole_0(k1_xboole_0, A_188)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2040])).
% 4.24/1.80  tff(c_2076, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2062])).
% 4.24/1.80  tff(c_2687, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2656, c_2076])).
% 4.24/1.80  tff(c_2693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1991, c_2687])).
% 4.24/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.80  
% 4.24/1.80  Inference rules
% 4.24/1.80  ----------------------
% 4.24/1.80  #Ref     : 0
% 4.24/1.80  #Sup     : 605
% 4.24/1.80  #Fact    : 0
% 4.24/1.80  #Define  : 0
% 4.24/1.80  #Split   : 11
% 4.24/1.80  #Chain   : 0
% 4.24/1.80  #Close   : 0
% 4.24/1.80  
% 4.24/1.80  Ordering : KBO
% 4.24/1.80  
% 4.24/1.80  Simplification rules
% 4.24/1.80  ----------------------
% 4.24/1.80  #Subsume      : 149
% 4.24/1.80  #Demod        : 257
% 4.24/1.80  #Tautology    : 312
% 4.24/1.80  #SimpNegUnit  : 16
% 4.24/1.80  #BackRed      : 13
% 4.24/1.80  
% 4.24/1.80  #Partial instantiations: 0
% 4.24/1.80  #Strategies tried      : 1
% 4.24/1.80  
% 4.24/1.80  Timing (in seconds)
% 4.24/1.80  ----------------------
% 4.30/1.81  Preprocessing        : 0.35
% 4.30/1.81  Parsing              : 0.18
% 4.30/1.81  CNF conversion       : 0.03
% 4.30/1.81  Main loop            : 0.65
% 4.30/1.81  Inferencing          : 0.23
% 4.30/1.81  Reduction            : 0.22
% 4.30/1.81  Demodulation         : 0.16
% 4.30/1.81  BG Simplification    : 0.03
% 4.30/1.81  Subsumption          : 0.12
% 4.30/1.81  Abstraction          : 0.03
% 4.30/1.81  MUC search           : 0.00
% 4.30/1.81  Cooper               : 0.00
% 4.30/1.81  Total                : 1.06
% 4.30/1.81  Index Insertion      : 0.00
% 4.30/1.81  Index Deletion       : 0.00
% 4.30/1.81  Index Matching       : 0.00
% 4.30/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
