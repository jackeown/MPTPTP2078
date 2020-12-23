%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 740 expanded)
%              Number of leaves         :   31 ( 265 expanded)
%              Depth                    :   16
%              Number of atoms          :  600 (3000 expanded)
%              Number of equality atoms :   48 ( 117 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( r2_hidden(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,B)
                    & r2_hidden(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_74,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | r1_tarski('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_85,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_87,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,B_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_96,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(A_107,C_108)
      | ~ r1_tarski(B_109,C_108)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5022,plain,(
    ! [A_437] :
      ( r1_tarski(A_437,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_437,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_95,c_96])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v3_pre_topc('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_86,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_84,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_82,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_103,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_64,plain,(
    ! [D_102] :
      ( ~ r2_hidden('#skF_6',D_102)
      | ~ r1_tarski(D_102,'#skF_7')
      | ~ v3_pre_topc(D_102,'#skF_5')
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1089,plain,(
    ~ m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1074,plain,(
    ! [A_230,B_231] :
      ( v3_pre_topc(k1_tops_1(A_230,B_231),A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1081,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1074])).

tff(c_1088,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1081])).

tff(c_16,plain,(
    ! [B_26,D_32,C_30,A_18] :
      ( k1_tops_1(B_26,D_32) = D_32
      | ~ v3_pre_topc(D_32,B_26)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2252,plain,(
    ! [C_363,A_364] :
      ( ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_2255,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_2252])).

tff(c_2266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2255])).

tff(c_2268,plain,(
    ! [B_365,D_366] :
      ( k1_tops_1(B_365,D_366) = D_366
      | ~ v3_pre_topc(D_366,B_365)
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0(B_365)))
      | ~ l1_pre_topc(B_365) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_2271,plain,
    ( k1_tops_1('#skF_5','#skF_8') = '#skF_8'
    | ~ v3_pre_topc('#skF_8','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_2268])).

tff(c_2281,plain,(
    k1_tops_1('#skF_5','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_86,c_2271])).

tff(c_12,plain,(
    ! [A_11,B_15,C_17] :
      ( r1_tarski(k1_tops_1(A_11,B_15),k1_tops_1(A_11,C_17))
      | ~ r1_tarski(B_15,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2338,plain,(
    ! [C_17] :
      ( r1_tarski('#skF_8',k1_tops_1('#skF_5',C_17))
      | ~ r1_tarski('#skF_8',C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2281,c_12])).

tff(c_2846,plain,(
    ! [C_377] :
      ( r1_tarski('#skF_8',k1_tops_1('#skF_5',C_377))
      | ~ r1_tarski('#skF_8',C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_103,c_2338])).

tff(c_2860,plain,
    ( r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_2846])).

tff(c_2870,plain,(
    r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2860])).

tff(c_146,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k1_tops_1(A_115,B_116),B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_153,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_160,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_153])).

tff(c_101,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_107,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_95,c_96])).

tff(c_2478,plain,(
    ! [B_370,A_371] :
      ( k1_tops_1(B_370,A_371) = A_371
      | ~ v3_pre_topc(A_371,B_370)
      | ~ l1_pre_topc(B_370)
      | ~ r1_tarski(A_371,u1_struct_0(B_370)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2268])).

tff(c_2520,plain,(
    ! [A_107] :
      ( k1_tops_1('#skF_5',A_107) = A_107
      | ~ v3_pre_topc(A_107,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_107,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_101,c_2478])).

tff(c_2677,plain,(
    ! [A_376] :
      ( k1_tops_1('#skF_5',A_376) = A_376
      | ~ v3_pre_topc(A_376,'#skF_5')
      | ~ r1_tarski(A_376,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2520])).

tff(c_2704,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1088,c_2677])).

tff(c_2723,plain,(
    k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_2704])).

tff(c_157,plain,(
    ! [A_115,A_4] :
      ( r1_tarski(k1_tops_1(A_115,A_4),A_4)
      | ~ l1_pre_topc(A_115)
      | ~ r1_tarski(A_4,u1_struct_0(A_115)) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_2801,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),k1_tops_1('#skF_5','#skF_7'))
    | ~ l1_pre_topc('#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_157])).

tff(c_2844,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2801])).

tff(c_3449,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2844])).

tff(c_3467,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_101,c_3449])).

tff(c_3484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_3467])).

tff(c_3486,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2844])).

tff(c_3598,plain,(
    ! [C_391,A_392,B_393] :
      ( m1_connsp_2(C_391,A_392,B_393)
      | ~ r2_hidden(B_393,k1_tops_1(A_392,C_391))
      | ~ m1_subset_1(C_391,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ m1_subset_1(B_393,u1_struct_0(A_392))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3604,plain,(
    ! [B_393] :
      ( m1_connsp_2(k1_tops_1('#skF_5','#skF_7'),'#skF_5',B_393)
      | ~ r2_hidden(B_393,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_3598])).

tff(c_3622,plain,(
    ! [B_393] :
      ( m1_connsp_2(k1_tops_1('#skF_5','#skF_7'),'#skF_5',B_393)
      | ~ r2_hidden(B_393,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3604])).

tff(c_3623,plain,(
    ! [B_393] :
      ( m1_connsp_2(k1_tops_1('#skF_5','#skF_7'),'#skF_5',B_393)
      | ~ r2_hidden(B_393,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3622])).

tff(c_3697,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3623])).

tff(c_3700,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_3697])).

tff(c_3704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_3700])).

tff(c_3706,plain,(
    m1_subset_1(k1_tops_1('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3623])).

tff(c_4542,plain,(
    ! [C_423,B_424,D_425,A_426] :
      ( r2_hidden(C_423,B_424)
      | ~ r2_hidden(C_423,D_425)
      | ~ r1_tarski(D_425,B_424)
      | ~ v3_pre_topc(D_425,A_426)
      | ~ m1_subset_1(D_425,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ v3_pre_topc(B_424,A_426)
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4755,plain,(
    ! [B_431,A_432] :
      ( r2_hidden('#skF_6',B_431)
      | ~ r1_tarski('#skF_8',B_431)
      | ~ v3_pre_topc('#skF_8',A_432)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ v3_pre_topc(B_431,A_432)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432) ) ),
    inference(resolution,[status(thm)],[c_84,c_4542])).

tff(c_4757,plain,(
    ! [B_431] :
      ( r2_hidden('#skF_6',B_431)
      | ~ r1_tarski('#skF_8',B_431)
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ v3_pre_topc(B_431,'#skF_5')
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_103,c_4755])).

tff(c_4945,plain,(
    ! [B_434] :
      ( r2_hidden('#skF_6',B_434)
      | ~ r1_tarski('#skF_8',B_434)
      | ~ v3_pre_topc(B_434,'#skF_5')
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_86,c_4757])).

tff(c_4952,plain,
    ( r2_hidden('#skF_6',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_8',k1_tops_1('#skF_5','#skF_7'))
    | ~ v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3706,c_4945])).

tff(c_4972,plain,(
    r2_hidden('#skF_6',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_2870,c_4952])).

tff(c_48,plain,(
    ! [C_79,A_73,B_77] :
      ( m1_connsp_2(C_79,A_73,B_77)
      | ~ r2_hidden(B_77,k1_tops_1(A_73,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_77,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4986,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4972,c_48])).

tff(c_4990,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_4986])).

tff(c_4992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1089,c_4990])).

tff(c_4996,plain,(
    ! [D_435] :
      ( ~ r2_hidden('#skF_6',D_435)
      | ~ r1_tarski(D_435,'#skF_7')
      | ~ v3_pre_topc(D_435,'#skF_5')
      | ~ m1_subset_1(D_435,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4999,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_4996])).

tff(c_5010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_84,c_4999])).

tff(c_5012,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_5016,plain,(
    ~ r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_5012])).

tff(c_5025,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5022,c_5016])).

tff(c_5031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_5025])).

tff(c_5032,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_5085,plain,(
    ! [A_448,B_449] :
      ( r1_tarski(k1_tops_1(A_448,B_449),B_449)
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ l1_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5090,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_5085])).

tff(c_5094,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5090])).

tff(c_5127,plain,(
    ! [A_453,B_454] :
      ( v3_pre_topc(k1_tops_1(A_453,B_454),A_453)
      | ~ m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5132,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_5127])).

tff(c_5136,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5132])).

tff(c_5034,plain,(
    ! [A_438,B_439] :
      ( r1_tarski(A_438,B_439)
      | ~ m1_subset_1(A_438,k1_zfmisc_1(B_439)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5042,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_5034])).

tff(c_5044,plain,(
    ! [A_440,C_441,B_442] :
      ( r1_tarski(A_440,C_441)
      | ~ r1_tarski(B_442,C_441)
      | ~ r1_tarski(A_440,B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5049,plain,(
    ! [A_440] :
      ( r1_tarski(A_440,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_440,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5042,c_5044])).

tff(c_5595,plain,(
    ! [C_539,A_540] :
      ( ~ m1_subset_1(C_539,k1_zfmisc_1(u1_struct_0(A_540)))
      | ~ l1_pre_topc(A_540)
      | ~ v2_pre_topc(A_540) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_5602,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_5595])).

tff(c_5607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5602])).

tff(c_5609,plain,(
    ! [B_541,D_542] :
      ( k1_tops_1(B_541,D_542) = D_542
      | ~ v3_pre_topc(D_542,B_541)
      | ~ m1_subset_1(D_542,k1_zfmisc_1(u1_struct_0(B_541)))
      | ~ l1_pre_topc(B_541) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_5625,plain,(
    ! [B_543,A_544] :
      ( k1_tops_1(B_543,A_544) = A_544
      | ~ v3_pre_topc(A_544,B_543)
      | ~ l1_pre_topc(B_543)
      | ~ r1_tarski(A_544,u1_struct_0(B_543)) ) ),
    inference(resolution,[status(thm)],[c_6,c_5609])).

tff(c_5649,plain,(
    ! [A_440] :
      ( k1_tops_1('#skF_5',A_440) = A_440
      | ~ v3_pre_topc(A_440,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_440,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5049,c_5625])).

tff(c_5669,plain,(
    ! [A_545] :
      ( k1_tops_1('#skF_5',A_545) = A_545
      | ~ v3_pre_topc(A_545,'#skF_5')
      | ~ r1_tarski(A_545,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5649])).

tff(c_5684,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_5136,c_5669])).

tff(c_5696,plain,(
    k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5094,c_5684])).

tff(c_6687,plain,(
    ! [B_579,A_580,C_581] :
      ( r2_hidden(B_579,k1_tops_1(A_580,C_581))
      | ~ m1_connsp_2(C_581,A_580,B_579)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(u1_struct_0(A_580)))
      | ~ m1_subset_1(B_579,u1_struct_0(A_580))
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580)
      | v2_struct_0(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6698,plain,(
    ! [B_579] :
      ( r2_hidden(B_579,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_579)
      | ~ m1_subset_1(B_579,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_6687])).

tff(c_6708,plain,(
    ! [B_579] :
      ( r2_hidden(B_579,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_579)
      | ~ m1_subset_1(B_579,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_6698])).

tff(c_6710,plain,(
    ! [B_582] :
      ( r2_hidden(B_582,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_582)
      | ~ m1_subset_1(B_582,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6708])).

tff(c_14,plain,(
    ! [C_30,A_18,D_32,B_26] :
      ( v3_pre_topc(C_30,A_18)
      | k1_tops_1(A_18,C_30) != C_30
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5863,plain,(
    ! [D_546,B_547] :
      ( ~ m1_subset_1(D_546,k1_zfmisc_1(u1_struct_0(B_547)))
      | ~ l1_pre_topc(B_547) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_5870,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_5863])).

tff(c_5875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5870])).

tff(c_5950,plain,(
    ! [C_553,A_554] :
      ( v3_pre_topc(C_553,A_554)
      | k1_tops_1(A_554,C_553) != C_553
      | ~ m1_subset_1(C_553,k1_zfmisc_1(u1_struct_0(A_554)))
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_5967,plain,(
    ! [A_555,A_556] :
      ( v3_pre_topc(A_555,A_556)
      | k1_tops_1(A_556,A_555) != A_555
      | ~ l1_pre_topc(A_556)
      | ~ v2_pre_topc(A_556)
      | ~ r1_tarski(A_555,u1_struct_0(A_556)) ) ),
    inference(resolution,[status(thm)],[c_6,c_5950])).

tff(c_5997,plain,(
    ! [A_440] :
      ( v3_pre_topc(A_440,'#skF_5')
      | k1_tops_1('#skF_5',A_440) != A_440
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_440,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5049,c_5967])).

tff(c_6024,plain,(
    ! [A_557] :
      ( v3_pre_topc(A_557,'#skF_5')
      | k1_tops_1('#skF_5',A_557) != A_557
      | ~ r1_tarski(A_557,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5997])).

tff(c_5033,plain,(
    ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,(
    ! [D_102] :
      ( ~ r2_hidden('#skF_6',D_102)
      | ~ r1_tarski(D_102,'#skF_7')
      | ~ v3_pre_topc(D_102,'#skF_5')
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v3_pre_topc('#skF_8','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5052,plain,(
    ! [D_443] :
      ( ~ r2_hidden('#skF_6',D_443)
      | ~ r1_tarski(D_443,'#skF_7')
      | ~ v3_pre_topc(D_443,'#skF_5')
      | ~ m1_subset_1(D_443,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5033,c_76])).

tff(c_5154,plain,(
    ! [A_459] :
      ( ~ r2_hidden('#skF_6',A_459)
      | ~ r1_tarski(A_459,'#skF_7')
      | ~ v3_pre_topc(A_459,'#skF_5')
      | ~ r1_tarski(A_459,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_5052])).

tff(c_5166,plain,(
    ! [A_440] :
      ( ~ r2_hidden('#skF_6',A_440)
      | ~ v3_pre_topc(A_440,'#skF_5')
      | ~ r1_tarski(A_440,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5049,c_5154])).

tff(c_6038,plain,(
    ! [A_557] :
      ( ~ r2_hidden('#skF_6',A_557)
      | k1_tops_1('#skF_5',A_557) != A_557
      | ~ r1_tarski(A_557,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6024,c_5166])).

tff(c_6718,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) != k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6710,c_6038])).

tff(c_6737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5032,c_5094,c_5696,c_6718])).

tff(c_6738,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6759,plain,(
    ! [A_589,B_590] :
      ( r1_tarski(k1_tops_1(A_589,B_590),B_590)
      | ~ m1_subset_1(B_590,k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ l1_pre_topc(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6764,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_6759])).

tff(c_6768,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6764])).

tff(c_8619,plain,(
    ! [A_733,B_734] :
      ( v3_pre_topc(k1_tops_1(A_733,B_734),A_733)
      | ~ m1_subset_1(B_734,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ l1_pre_topc(A_733)
      | ~ v2_pre_topc(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8624,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_8619])).

tff(c_8628,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_8624])).

tff(c_6741,plain,(
    ! [A_583,B_584] :
      ( r1_tarski(A_583,B_584)
      | ~ m1_subset_1(A_583,k1_zfmisc_1(B_584)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6749,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_6741])).

tff(c_6750,plain,(
    ! [A_585,C_586,B_587] :
      ( r1_tarski(A_585,C_586)
      | ~ r1_tarski(B_587,C_586)
      | ~ r1_tarski(A_585,B_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6753,plain,(
    ! [A_585] :
      ( r1_tarski(A_585,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_585,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6749,c_6750])).

tff(c_9043,plain,(
    ! [C_818,A_819] :
      ( ~ m1_subset_1(C_818,k1_zfmisc_1(u1_struct_0(A_819)))
      | ~ l1_pre_topc(A_819)
      | ~ v2_pre_topc(A_819) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_9050,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_9043])).

tff(c_9055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_9050])).

tff(c_9067,plain,(
    ! [B_821,D_822] :
      ( k1_tops_1(B_821,D_822) = D_822
      | ~ v3_pre_topc(D_822,B_821)
      | ~ m1_subset_1(D_822,k1_zfmisc_1(u1_struct_0(B_821)))
      | ~ l1_pre_topc(B_821) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_9097,plain,(
    ! [B_826,A_827] :
      ( k1_tops_1(B_826,A_827) = A_827
      | ~ v3_pre_topc(A_827,B_826)
      | ~ l1_pre_topc(B_826)
      | ~ r1_tarski(A_827,u1_struct_0(B_826)) ) ),
    inference(resolution,[status(thm)],[c_6,c_9067])).

tff(c_9127,plain,(
    ! [A_585] :
      ( k1_tops_1('#skF_5',A_585) = A_585
      | ~ v3_pre_topc(A_585,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_585,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6753,c_9097])).

tff(c_9154,plain,(
    ! [A_828] :
      ( k1_tops_1('#skF_5',A_828) = A_828
      | ~ v3_pre_topc(A_828,'#skF_5')
      | ~ r1_tarski(A_828,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9127])).

tff(c_9172,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_8628,c_9154])).

tff(c_9188,plain,(
    k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6768,c_9172])).

tff(c_9932,plain,(
    ! [B_849,A_850,C_851] :
      ( r2_hidden(B_849,k1_tops_1(A_850,C_851))
      | ~ m1_connsp_2(C_851,A_850,B_849)
      | ~ m1_subset_1(C_851,k1_zfmisc_1(u1_struct_0(A_850)))
      | ~ m1_subset_1(B_849,u1_struct_0(A_850))
      | ~ l1_pre_topc(A_850)
      | ~ v2_pre_topc(A_850)
      | v2_struct_0(A_850) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9941,plain,(
    ! [B_849] :
      ( r2_hidden(B_849,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_849)
      | ~ m1_subset_1(B_849,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_9932])).

tff(c_9950,plain,(
    ! [B_849] :
      ( r2_hidden(B_849,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_849)
      | ~ m1_subset_1(B_849,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_9941])).

tff(c_9952,plain,(
    ! [B_852] :
      ( r2_hidden(B_852,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_852)
      | ~ m1_subset_1(B_852,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9950])).

tff(c_8951,plain,(
    ! [D_811,B_812] :
      ( ~ m1_subset_1(D_811,k1_zfmisc_1(u1_struct_0(B_812)))
      | ~ l1_pre_topc(B_812) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_8958,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_8951])).

tff(c_8963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8958])).

tff(c_8965,plain,(
    ! [C_813,A_814] :
      ( v3_pre_topc(C_813,A_814)
      | k1_tops_1(A_814,C_813) != C_813
      | ~ m1_subset_1(C_813,k1_zfmisc_1(u1_struct_0(A_814)))
      | ~ l1_pre_topc(A_814)
      | ~ v2_pre_topc(A_814) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_8982,plain,(
    ! [A_815,A_816] :
      ( v3_pre_topc(A_815,A_816)
      | k1_tops_1(A_816,A_815) != A_815
      | ~ l1_pre_topc(A_816)
      | ~ v2_pre_topc(A_816)
      | ~ r1_tarski(A_815,u1_struct_0(A_816)) ) ),
    inference(resolution,[status(thm)],[c_6,c_8965])).

tff(c_9009,plain,(
    ! [A_585] :
      ( v3_pre_topc(A_585,'#skF_5')
      | k1_tops_1('#skF_5',A_585) != A_585
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_585,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6753,c_8982])).

tff(c_9033,plain,(
    ! [A_817] :
      ( v3_pre_topc(A_817,'#skF_5')
      | k1_tops_1('#skF_5',A_817) != A_817
      | ~ r1_tarski(A_817,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_9009])).

tff(c_6739,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [D_102] :
      ( ~ r2_hidden('#skF_6',D_102)
      | ~ r1_tarski(D_102,'#skF_7')
      | ~ v3_pre_topc(D_102,'#skF_5')
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tarski('#skF_8','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8576,plain,(
    ! [D_728] :
      ( ~ r2_hidden('#skF_6',D_728)
      | ~ r1_tarski(D_728,'#skF_7')
      | ~ v3_pre_topc(D_728,'#skF_5')
      | ~ m1_subset_1(D_728,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6739,c_72])).

tff(c_8598,plain,(
    ! [A_731] :
      ( ~ r2_hidden('#skF_6',A_731)
      | ~ r1_tarski(A_731,'#skF_7')
      | ~ v3_pre_topc(A_731,'#skF_5')
      | ~ r1_tarski(A_731,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_8576])).

tff(c_8610,plain,(
    ! [A_585] :
      ( ~ r2_hidden('#skF_6',A_585)
      | ~ v3_pre_topc(A_585,'#skF_5')
      | ~ r1_tarski(A_585,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6753,c_8598])).

tff(c_9041,plain,(
    ! [A_817] :
      ( ~ r2_hidden('#skF_6',A_817)
      | k1_tops_1('#skF_5',A_817) != A_817
      | ~ r1_tarski(A_817,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9033,c_8610])).

tff(c_9958,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) != k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_9952,c_9041])).

tff(c_9976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6738,c_6768,c_9188,c_9958])).

tff(c_9977,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_10007,plain,(
    ! [A_861,B_862] :
      ( r1_tarski(k1_tops_1(A_861,B_862),B_862)
      | ~ m1_subset_1(B_862,k1_zfmisc_1(u1_struct_0(A_861)))
      | ~ l1_pre_topc(A_861) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10012,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10007])).

tff(c_10016,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10012])).

tff(c_10037,plain,(
    ! [A_865,B_866] :
      ( v3_pre_topc(k1_tops_1(A_865,B_866),A_865)
      | ~ m1_subset_1(B_866,k1_zfmisc_1(u1_struct_0(A_865)))
      | ~ l1_pre_topc(A_865)
      | ~ v2_pre_topc(A_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10042,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10037])).

tff(c_10046,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_10042])).

tff(c_9980,plain,(
    ! [A_853,B_854] :
      ( r1_tarski(A_853,B_854)
      | ~ m1_subset_1(A_853,k1_zfmisc_1(B_854)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9988,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_9980])).

tff(c_9990,plain,(
    ! [A_855,C_856,B_857] :
      ( r1_tarski(A_855,C_856)
      | ~ r1_tarski(B_857,C_856)
      | ~ r1_tarski(A_855,B_857) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9993,plain,(
    ! [A_855] :
      ( r1_tarski(A_855,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_855,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9988,c_9990])).

tff(c_10470,plain,(
    ! [C_950,A_951] :
      ( ~ m1_subset_1(C_950,k1_zfmisc_1(u1_struct_0(A_951)))
      | ~ l1_pre_topc(A_951)
      | ~ v2_pre_topc(A_951) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_10477,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10470])).

tff(c_10482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_10477])).

tff(c_10512,plain,(
    ! [B_957,D_958] :
      ( k1_tops_1(B_957,D_958) = D_958
      | ~ v3_pre_topc(D_958,B_957)
      | ~ m1_subset_1(D_958,k1_zfmisc_1(u1_struct_0(B_957)))
      | ~ l1_pre_topc(B_957) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_10529,plain,(
    ! [B_959,A_960] :
      ( k1_tops_1(B_959,A_960) = A_960
      | ~ v3_pre_topc(A_960,B_959)
      | ~ l1_pre_topc(B_959)
      | ~ r1_tarski(A_960,u1_struct_0(B_959)) ) ),
    inference(resolution,[status(thm)],[c_6,c_10512])).

tff(c_10559,plain,(
    ! [A_855] :
      ( k1_tops_1('#skF_5',A_855) = A_855
      | ~ v3_pre_topc(A_855,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_855,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9993,c_10529])).

tff(c_10586,plain,(
    ! [A_961] :
      ( k1_tops_1('#skF_5',A_961) = A_961
      | ~ v3_pre_topc(A_961,'#skF_5')
      | ~ r1_tarski(A_961,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10559])).

tff(c_10604,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10046,c_10586])).

tff(c_10617,plain,(
    k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) = k1_tops_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10016,c_10604])).

tff(c_11835,plain,(
    ! [B_1002,A_1003,C_1004] :
      ( r2_hidden(B_1002,k1_tops_1(A_1003,C_1004))
      | ~ m1_connsp_2(C_1004,A_1003,B_1002)
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(u1_struct_0(A_1003)))
      | ~ m1_subset_1(B_1002,u1_struct_0(A_1003))
      | ~ l1_pre_topc(A_1003)
      | ~ v2_pre_topc(A_1003)
      | v2_struct_0(A_1003) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_11846,plain,(
    ! [B_1002] :
      ( r2_hidden(B_1002,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_1002)
      | ~ m1_subset_1(B_1002,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_11835])).

tff(c_11856,plain,(
    ! [B_1002] :
      ( r2_hidden(B_1002,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_1002)
      | ~ m1_subset_1(B_1002,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_11846])).

tff(c_11858,plain,(
    ! [B_1005] :
      ( r2_hidden(B_1005,k1_tops_1('#skF_5','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_5',B_1005)
      | ~ m1_subset_1(B_1005,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_11856])).

tff(c_10387,plain,(
    ! [D_944,B_945] :
      ( ~ m1_subset_1(D_944,k1_zfmisc_1(u1_struct_0(B_945)))
      | ~ l1_pre_topc(B_945) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_10394,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_10387])).

tff(c_10399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10394])).

tff(c_10401,plain,(
    ! [C_946,A_947] :
      ( v3_pre_topc(C_946,A_947)
      | k1_tops_1(A_947,C_946) != C_946
      | ~ m1_subset_1(C_946,k1_zfmisc_1(u1_struct_0(A_947)))
      | ~ l1_pre_topc(A_947)
      | ~ v2_pre_topc(A_947) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_10418,plain,(
    ! [A_948,A_949] :
      ( v3_pre_topc(A_948,A_949)
      | k1_tops_1(A_949,A_948) != A_948
      | ~ l1_pre_topc(A_949)
      | ~ v2_pre_topc(A_949)
      | ~ r1_tarski(A_948,u1_struct_0(A_949)) ) ),
    inference(resolution,[status(thm)],[c_6,c_10401])).

tff(c_10445,plain,(
    ! [A_855] :
      ( v3_pre_topc(A_855,'#skF_5')
      | k1_tops_1('#skF_5',A_855) != A_855
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ r1_tarski(A_855,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9993,c_10418])).

tff(c_10484,plain,(
    ! [A_952] :
      ( v3_pre_topc(A_952,'#skF_5')
      | k1_tops_1('#skF_5',A_952) != A_952
      | ~ r1_tarski(A_952,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_10445])).

tff(c_9978,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [D_102] :
      ( ~ r2_hidden('#skF_6',D_102)
      | ~ r1_tarski(D_102,'#skF_7')
      | ~ v3_pre_topc(D_102,'#skF_5')
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r2_hidden('#skF_6','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10024,plain,(
    ! [D_863] :
      ( ~ r2_hidden('#skF_6',D_863)
      | ~ r1_tarski(D_863,'#skF_7')
      | ~ v3_pre_topc(D_863,'#skF_5')
      | ~ m1_subset_1(D_863,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9978,c_68])).

tff(c_10059,plain,(
    ! [A_869] :
      ( ~ r2_hidden('#skF_6',A_869)
      | ~ r1_tarski(A_869,'#skF_7')
      | ~ v3_pre_topc(A_869,'#skF_5')
      | ~ r1_tarski(A_869,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_10024])).

tff(c_10071,plain,(
    ! [A_855] :
      ( ~ r2_hidden('#skF_6',A_855)
      | ~ v3_pre_topc(A_855,'#skF_5')
      | ~ r1_tarski(A_855,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9993,c_10059])).

tff(c_10491,plain,(
    ! [A_952] :
      ( ~ r2_hidden('#skF_6',A_952)
      | k1_tops_1('#skF_5',A_952) != A_952
      | ~ r1_tarski(A_952,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10484,c_10071])).

tff(c_11868,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_7')) != k1_tops_1('#skF_5','#skF_7')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_7'),'#skF_7')
    | ~ m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_11858,c_10491])).

tff(c_11889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9977,c_10016,c_10617,c_11868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:26:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.31  
% 10.17/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.31  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 10.17/3.31  
% 10.17/3.31  %Foreground sorts:
% 10.17/3.31  
% 10.17/3.31  
% 10.17/3.31  %Background operators:
% 10.17/3.31  
% 10.17/3.31  
% 10.17/3.31  %Foreground operators:
% 10.17/3.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.17/3.31  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 10.17/3.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.17/3.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.17/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.17/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.17/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.17/3.31  tff('#skF_7', type, '#skF_7': $i).
% 10.17/3.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.17/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.17/3.31  tff('#skF_5', type, '#skF_5': $i).
% 10.17/3.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.17/3.31  tff('#skF_6', type, '#skF_6': $i).
% 10.17/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.17/3.31  tff('#skF_8', type, '#skF_8': $i).
% 10.17/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.17/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.17/3.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.17/3.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.17/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.17/3.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.17/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.17/3.31  
% 10.17/3.35  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 10.17/3.35  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.17/3.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.17/3.35  tff(f_43, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 10.17/3.35  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 10.17/3.35  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 10.17/3.35  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 10.17/3.35  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 10.17/3.35  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_1)).
% 10.17/3.35  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_74, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | r1_tarski('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_85, plain, (r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 10.17/3.35  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_87, plain, (![A_105, B_106]: (r1_tarski(A_105, B_106) | ~m1_subset_1(A_105, k1_zfmisc_1(B_106)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.17/3.35  tff(c_95, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_87])).
% 10.17/3.35  tff(c_96, plain, (![A_107, C_108, B_109]: (r1_tarski(A_107, C_108) | ~r1_tarski(B_109, C_108) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.35  tff(c_5022, plain, (![A_437]: (r1_tarski(A_437, u1_struct_0('#skF_5')) | ~r1_tarski(A_437, '#skF_7'))), inference(resolution, [status(thm)], [c_95, c_96])).
% 10.17/3.35  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.17/3.35  tff(c_78, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v3_pre_topc('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_86, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 10.17/3.35  tff(c_70, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_84, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_70])).
% 10.17/3.35  tff(c_82, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_103, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_82])).
% 10.17/3.35  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_64, plain, (![D_102]: (~r2_hidden('#skF_6', D_102) | ~r1_tarski(D_102, '#skF_7') | ~v3_pre_topc(D_102, '#skF_5') | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_1089, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_64])).
% 10.17/3.35  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_1074, plain, (![A_230, B_231]: (v3_pre_topc(k1_tops_1(A_230, B_231), A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/3.35  tff(c_1081, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1074])).
% 10.17/3.35  tff(c_1088, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1081])).
% 10.17/3.35  tff(c_16, plain, (![B_26, D_32, C_30, A_18]: (k1_tops_1(B_26, D_32)=D_32 | ~v3_pre_topc(D_32, B_26) | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_26))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.35  tff(c_2252, plain, (![C_363, A_364]: (~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0(A_364))) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364))), inference(splitLeft, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_2255, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_103, c_2252])).
% 10.17/3.35  tff(c_2266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2255])).
% 10.17/3.35  tff(c_2268, plain, (![B_365, D_366]: (k1_tops_1(B_365, D_366)=D_366 | ~v3_pre_topc(D_366, B_365) | ~m1_subset_1(D_366, k1_zfmisc_1(u1_struct_0(B_365))) | ~l1_pre_topc(B_365))), inference(splitRight, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_2271, plain, (k1_tops_1('#skF_5', '#skF_8')='#skF_8' | ~v3_pre_topc('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_103, c_2268])).
% 10.17/3.35  tff(c_2281, plain, (k1_tops_1('#skF_5', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_86, c_2271])).
% 10.17/3.35  tff(c_12, plain, (![A_11, B_15, C_17]: (r1_tarski(k1_tops_1(A_11, B_15), k1_tops_1(A_11, C_17)) | ~r1_tarski(B_15, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.17/3.35  tff(c_2338, plain, (![C_17]: (r1_tarski('#skF_8', k1_tops_1('#skF_5', C_17)) | ~r1_tarski('#skF_8', C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2281, c_12])).
% 10.17/3.35  tff(c_2846, plain, (![C_377]: (r1_tarski('#skF_8', k1_tops_1('#skF_5', C_377)) | ~r1_tarski('#skF_8', C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_103, c_2338])).
% 10.17/3.35  tff(c_2860, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_2846])).
% 10.17/3.35  tff(c_2870, plain, (r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2860])).
% 10.17/3.35  tff(c_146, plain, (![A_115, B_116]: (r1_tarski(k1_tops_1(A_115, B_116), B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.35  tff(c_153, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_146])).
% 10.17/3.35  tff(c_160, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_153])).
% 10.17/3.35  tff(c_101, plain, (![A_107]: (r1_tarski(A_107, u1_struct_0('#skF_5')) | ~r1_tarski(A_107, '#skF_7'))), inference(resolution, [status(thm)], [c_95, c_96])).
% 10.17/3.35  tff(c_2478, plain, (![B_370, A_371]: (k1_tops_1(B_370, A_371)=A_371 | ~v3_pre_topc(A_371, B_370) | ~l1_pre_topc(B_370) | ~r1_tarski(A_371, u1_struct_0(B_370)))), inference(resolution, [status(thm)], [c_6, c_2268])).
% 10.17/3.35  tff(c_2520, plain, (![A_107]: (k1_tops_1('#skF_5', A_107)=A_107 | ~v3_pre_topc(A_107, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_107, '#skF_7'))), inference(resolution, [status(thm)], [c_101, c_2478])).
% 10.17/3.35  tff(c_2677, plain, (![A_376]: (k1_tops_1('#skF_5', A_376)=A_376 | ~v3_pre_topc(A_376, '#skF_5') | ~r1_tarski(A_376, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2520])).
% 10.17/3.35  tff(c_2704, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_1088, c_2677])).
% 10.17/3.35  tff(c_2723, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_2704])).
% 10.17/3.35  tff(c_157, plain, (![A_115, A_4]: (r1_tarski(k1_tops_1(A_115, A_4), A_4) | ~l1_pre_topc(A_115) | ~r1_tarski(A_4, u1_struct_0(A_115)))), inference(resolution, [status(thm)], [c_6, c_146])).
% 10.17/3.35  tff(c_2801, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), k1_tops_1('#skF_5', '#skF_7')) | ~l1_pre_topc('#skF_5') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2723, c_157])).
% 10.17/3.35  tff(c_2844, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2801])).
% 10.17/3.35  tff(c_3449, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_2844])).
% 10.17/3.35  tff(c_3467, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_101, c_3449])).
% 10.17/3.35  tff(c_3484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_3467])).
% 10.17/3.35  tff(c_3486, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2844])).
% 10.17/3.35  tff(c_3598, plain, (![C_391, A_392, B_393]: (m1_connsp_2(C_391, A_392, B_393) | ~r2_hidden(B_393, k1_tops_1(A_392, C_391)) | ~m1_subset_1(C_391, k1_zfmisc_1(u1_struct_0(A_392))) | ~m1_subset_1(B_393, u1_struct_0(A_392)) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.17/3.35  tff(c_3604, plain, (![B_393]: (m1_connsp_2(k1_tops_1('#skF_5', '#skF_7'), '#skF_5', B_393) | ~r2_hidden(B_393, k1_tops_1('#skF_5', '#skF_7')) | ~m1_subset_1(k1_tops_1('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_393, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2723, c_3598])).
% 10.17/3.35  tff(c_3622, plain, (![B_393]: (m1_connsp_2(k1_tops_1('#skF_5', '#skF_7'), '#skF_5', B_393) | ~r2_hidden(B_393, k1_tops_1('#skF_5', '#skF_7')) | ~m1_subset_1(k1_tops_1('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_393, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3604])).
% 10.17/3.35  tff(c_3623, plain, (![B_393]: (m1_connsp_2(k1_tops_1('#skF_5', '#skF_7'), '#skF_5', B_393) | ~r2_hidden(B_393, k1_tops_1('#skF_5', '#skF_7')) | ~m1_subset_1(k1_tops_1('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_393, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_3622])).
% 10.17/3.35  tff(c_3697, plain, (~m1_subset_1(k1_tops_1('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_3623])).
% 10.17/3.35  tff(c_3700, plain, (~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_3697])).
% 10.17/3.35  tff(c_3704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3486, c_3700])).
% 10.17/3.35  tff(c_3706, plain, (m1_subset_1(k1_tops_1('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_3623])).
% 10.17/3.35  tff(c_4542, plain, (![C_423, B_424, D_425, A_426]: (r2_hidden(C_423, B_424) | ~r2_hidden(C_423, D_425) | ~r1_tarski(D_425, B_424) | ~v3_pre_topc(D_425, A_426) | ~m1_subset_1(D_425, k1_zfmisc_1(u1_struct_0(A_426))) | ~v3_pre_topc(B_424, A_426) | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.17/3.35  tff(c_4755, plain, (![B_431, A_432]: (r2_hidden('#skF_6', B_431) | ~r1_tarski('#skF_8', B_431) | ~v3_pre_topc('#skF_8', A_432) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0(A_432))) | ~v3_pre_topc(B_431, A_432) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_432))) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432))), inference(resolution, [status(thm)], [c_84, c_4542])).
% 10.17/3.35  tff(c_4757, plain, (![B_431]: (r2_hidden('#skF_6', B_431) | ~r1_tarski('#skF_8', B_431) | ~v3_pre_topc('#skF_8', '#skF_5') | ~v3_pre_topc(B_431, '#skF_5') | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_103, c_4755])).
% 10.17/3.35  tff(c_4945, plain, (![B_434]: (r2_hidden('#skF_6', B_434) | ~r1_tarski('#skF_8', B_434) | ~v3_pre_topc(B_434, '#skF_5') | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_86, c_4757])).
% 10.17/3.35  tff(c_4952, plain, (r2_hidden('#skF_6', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_8', k1_tops_1('#skF_5', '#skF_7')) | ~v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_3706, c_4945])).
% 10.17/3.35  tff(c_4972, plain, (r2_hidden('#skF_6', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_2870, c_4952])).
% 10.17/3.35  tff(c_48, plain, (![C_79, A_73, B_77]: (m1_connsp_2(C_79, A_73, B_77) | ~r2_hidden(B_77, k1_tops_1(A_73, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_77, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.17/3.35  tff(c_4986, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4972, c_48])).
% 10.17/3.35  tff(c_4990, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_4986])).
% 10.17/3.35  tff(c_4992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1089, c_4990])).
% 10.17/3.35  tff(c_4996, plain, (![D_435]: (~r2_hidden('#skF_6', D_435) | ~r1_tarski(D_435, '#skF_7') | ~v3_pre_topc(D_435, '#skF_5') | ~m1_subset_1(D_435, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_64])).
% 10.17/3.35  tff(c_4999, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r1_tarski('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_103, c_4996])).
% 10.17/3.35  tff(c_5010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_84, c_4999])).
% 10.17/3.35  tff(c_5012, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_82])).
% 10.17/3.35  tff(c_5016, plain, (~r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_5012])).
% 10.17/3.35  tff(c_5025, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5022, c_5016])).
% 10.17/3.35  tff(c_5031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_5025])).
% 10.17/3.35  tff(c_5032, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 10.17/3.35  tff(c_5085, plain, (![A_448, B_449]: (r1_tarski(k1_tops_1(A_448, B_449), B_449) | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0(A_448))) | ~l1_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.35  tff(c_5090, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_5085])).
% 10.17/3.35  tff(c_5094, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5090])).
% 10.17/3.35  tff(c_5127, plain, (![A_453, B_454]: (v3_pre_topc(k1_tops_1(A_453, B_454), A_453) | ~m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0(A_453))) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/3.35  tff(c_5132, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_5127])).
% 10.17/3.35  tff(c_5136, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5132])).
% 10.17/3.35  tff(c_5034, plain, (![A_438, B_439]: (r1_tarski(A_438, B_439) | ~m1_subset_1(A_438, k1_zfmisc_1(B_439)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.17/3.35  tff(c_5042, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_5034])).
% 10.17/3.35  tff(c_5044, plain, (![A_440, C_441, B_442]: (r1_tarski(A_440, C_441) | ~r1_tarski(B_442, C_441) | ~r1_tarski(A_440, B_442))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.35  tff(c_5049, plain, (![A_440]: (r1_tarski(A_440, u1_struct_0('#skF_5')) | ~r1_tarski(A_440, '#skF_7'))), inference(resolution, [status(thm)], [c_5042, c_5044])).
% 10.17/3.35  tff(c_5595, plain, (![C_539, A_540]: (~m1_subset_1(C_539, k1_zfmisc_1(u1_struct_0(A_540))) | ~l1_pre_topc(A_540) | ~v2_pre_topc(A_540))), inference(splitLeft, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_5602, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_5595])).
% 10.17/3.35  tff(c_5607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5602])).
% 10.17/3.35  tff(c_5609, plain, (![B_541, D_542]: (k1_tops_1(B_541, D_542)=D_542 | ~v3_pre_topc(D_542, B_541) | ~m1_subset_1(D_542, k1_zfmisc_1(u1_struct_0(B_541))) | ~l1_pre_topc(B_541))), inference(splitRight, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_5625, plain, (![B_543, A_544]: (k1_tops_1(B_543, A_544)=A_544 | ~v3_pre_topc(A_544, B_543) | ~l1_pre_topc(B_543) | ~r1_tarski(A_544, u1_struct_0(B_543)))), inference(resolution, [status(thm)], [c_6, c_5609])).
% 10.17/3.35  tff(c_5649, plain, (![A_440]: (k1_tops_1('#skF_5', A_440)=A_440 | ~v3_pre_topc(A_440, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_440, '#skF_7'))), inference(resolution, [status(thm)], [c_5049, c_5625])).
% 10.17/3.35  tff(c_5669, plain, (![A_545]: (k1_tops_1('#skF_5', A_545)=A_545 | ~v3_pre_topc(A_545, '#skF_5') | ~r1_tarski(A_545, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5649])).
% 10.17/3.35  tff(c_5684, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_5136, c_5669])).
% 10.17/3.35  tff(c_5696, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5094, c_5684])).
% 10.17/3.35  tff(c_6687, plain, (![B_579, A_580, C_581]: (r2_hidden(B_579, k1_tops_1(A_580, C_581)) | ~m1_connsp_2(C_581, A_580, B_579) | ~m1_subset_1(C_581, k1_zfmisc_1(u1_struct_0(A_580))) | ~m1_subset_1(B_579, u1_struct_0(A_580)) | ~l1_pre_topc(A_580) | ~v2_pre_topc(A_580) | v2_struct_0(A_580))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.17/3.35  tff(c_6698, plain, (![B_579]: (r2_hidden(B_579, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_579) | ~m1_subset_1(B_579, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_6687])).
% 10.17/3.35  tff(c_6708, plain, (![B_579]: (r2_hidden(B_579, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_579) | ~m1_subset_1(B_579, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_6698])).
% 10.17/3.35  tff(c_6710, plain, (![B_582]: (r2_hidden(B_582, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_582) | ~m1_subset_1(B_582, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_6708])).
% 10.17/3.35  tff(c_14, plain, (![C_30, A_18, D_32, B_26]: (v3_pre_topc(C_30, A_18) | k1_tops_1(A_18, C_30)!=C_30 | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_26))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.35  tff(c_5863, plain, (![D_546, B_547]: (~m1_subset_1(D_546, k1_zfmisc_1(u1_struct_0(B_547))) | ~l1_pre_topc(B_547))), inference(splitLeft, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_5870, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_5863])).
% 10.17/3.35  tff(c_5875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_5870])).
% 10.17/3.35  tff(c_5950, plain, (![C_553, A_554]: (v3_pre_topc(C_553, A_554) | k1_tops_1(A_554, C_553)!=C_553 | ~m1_subset_1(C_553, k1_zfmisc_1(u1_struct_0(A_554))) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554))), inference(splitRight, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_5967, plain, (![A_555, A_556]: (v3_pre_topc(A_555, A_556) | k1_tops_1(A_556, A_555)!=A_555 | ~l1_pre_topc(A_556) | ~v2_pre_topc(A_556) | ~r1_tarski(A_555, u1_struct_0(A_556)))), inference(resolution, [status(thm)], [c_6, c_5950])).
% 10.17/3.35  tff(c_5997, plain, (![A_440]: (v3_pre_topc(A_440, '#skF_5') | k1_tops_1('#skF_5', A_440)!=A_440 | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_440, '#skF_7'))), inference(resolution, [status(thm)], [c_5049, c_5967])).
% 10.17/3.35  tff(c_6024, plain, (![A_557]: (v3_pre_topc(A_557, '#skF_5') | k1_tops_1('#skF_5', A_557)!=A_557 | ~r1_tarski(A_557, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5997])).
% 10.17/3.35  tff(c_5033, plain, (~v3_pre_topc('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 10.17/3.35  tff(c_76, plain, (![D_102]: (~r2_hidden('#skF_6', D_102) | ~r1_tarski(D_102, '#skF_7') | ~v3_pre_topc(D_102, '#skF_5') | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v3_pre_topc('#skF_8', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_5052, plain, (![D_443]: (~r2_hidden('#skF_6', D_443) | ~r1_tarski(D_443, '#skF_7') | ~v3_pre_topc(D_443, '#skF_5') | ~m1_subset_1(D_443, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_5033, c_76])).
% 10.17/3.35  tff(c_5154, plain, (![A_459]: (~r2_hidden('#skF_6', A_459) | ~r1_tarski(A_459, '#skF_7') | ~v3_pre_topc(A_459, '#skF_5') | ~r1_tarski(A_459, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_5052])).
% 10.17/3.35  tff(c_5166, plain, (![A_440]: (~r2_hidden('#skF_6', A_440) | ~v3_pre_topc(A_440, '#skF_5') | ~r1_tarski(A_440, '#skF_7'))), inference(resolution, [status(thm)], [c_5049, c_5154])).
% 10.17/3.35  tff(c_6038, plain, (![A_557]: (~r2_hidden('#skF_6', A_557) | k1_tops_1('#skF_5', A_557)!=A_557 | ~r1_tarski(A_557, '#skF_7'))), inference(resolution, [status(thm)], [c_6024, c_5166])).
% 10.17/3.35  tff(c_6718, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))!=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6710, c_6038])).
% 10.17/3.35  tff(c_6737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_5032, c_5094, c_5696, c_6718])).
% 10.17/3.35  tff(c_6738, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 10.17/3.35  tff(c_6759, plain, (![A_589, B_590]: (r1_tarski(k1_tops_1(A_589, B_590), B_590) | ~m1_subset_1(B_590, k1_zfmisc_1(u1_struct_0(A_589))) | ~l1_pre_topc(A_589))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.35  tff(c_6764, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_6759])).
% 10.17/3.35  tff(c_6768, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6764])).
% 10.17/3.35  tff(c_8619, plain, (![A_733, B_734]: (v3_pre_topc(k1_tops_1(A_733, B_734), A_733) | ~m1_subset_1(B_734, k1_zfmisc_1(u1_struct_0(A_733))) | ~l1_pre_topc(A_733) | ~v2_pre_topc(A_733))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/3.35  tff(c_8624, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_8619])).
% 10.17/3.35  tff(c_8628, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_8624])).
% 10.17/3.35  tff(c_6741, plain, (![A_583, B_584]: (r1_tarski(A_583, B_584) | ~m1_subset_1(A_583, k1_zfmisc_1(B_584)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.17/3.35  tff(c_6749, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_6741])).
% 10.17/3.35  tff(c_6750, plain, (![A_585, C_586, B_587]: (r1_tarski(A_585, C_586) | ~r1_tarski(B_587, C_586) | ~r1_tarski(A_585, B_587))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.35  tff(c_6753, plain, (![A_585]: (r1_tarski(A_585, u1_struct_0('#skF_5')) | ~r1_tarski(A_585, '#skF_7'))), inference(resolution, [status(thm)], [c_6749, c_6750])).
% 10.17/3.35  tff(c_9043, plain, (![C_818, A_819]: (~m1_subset_1(C_818, k1_zfmisc_1(u1_struct_0(A_819))) | ~l1_pre_topc(A_819) | ~v2_pre_topc(A_819))), inference(splitLeft, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_9050, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_9043])).
% 10.17/3.35  tff(c_9055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_9050])).
% 10.17/3.35  tff(c_9067, plain, (![B_821, D_822]: (k1_tops_1(B_821, D_822)=D_822 | ~v3_pre_topc(D_822, B_821) | ~m1_subset_1(D_822, k1_zfmisc_1(u1_struct_0(B_821))) | ~l1_pre_topc(B_821))), inference(splitRight, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_9097, plain, (![B_826, A_827]: (k1_tops_1(B_826, A_827)=A_827 | ~v3_pre_topc(A_827, B_826) | ~l1_pre_topc(B_826) | ~r1_tarski(A_827, u1_struct_0(B_826)))), inference(resolution, [status(thm)], [c_6, c_9067])).
% 10.17/3.35  tff(c_9127, plain, (![A_585]: (k1_tops_1('#skF_5', A_585)=A_585 | ~v3_pre_topc(A_585, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_585, '#skF_7'))), inference(resolution, [status(thm)], [c_6753, c_9097])).
% 10.17/3.35  tff(c_9154, plain, (![A_828]: (k1_tops_1('#skF_5', A_828)=A_828 | ~v3_pre_topc(A_828, '#skF_5') | ~r1_tarski(A_828, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9127])).
% 10.17/3.35  tff(c_9172, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_8628, c_9154])).
% 10.17/3.35  tff(c_9188, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6768, c_9172])).
% 10.17/3.35  tff(c_9932, plain, (![B_849, A_850, C_851]: (r2_hidden(B_849, k1_tops_1(A_850, C_851)) | ~m1_connsp_2(C_851, A_850, B_849) | ~m1_subset_1(C_851, k1_zfmisc_1(u1_struct_0(A_850))) | ~m1_subset_1(B_849, u1_struct_0(A_850)) | ~l1_pre_topc(A_850) | ~v2_pre_topc(A_850) | v2_struct_0(A_850))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.17/3.35  tff(c_9941, plain, (![B_849]: (r2_hidden(B_849, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_849) | ~m1_subset_1(B_849, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_9932])).
% 10.17/3.35  tff(c_9950, plain, (![B_849]: (r2_hidden(B_849, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_849) | ~m1_subset_1(B_849, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_9941])).
% 10.17/3.35  tff(c_9952, plain, (![B_852]: (r2_hidden(B_852, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_852) | ~m1_subset_1(B_852, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_9950])).
% 10.17/3.35  tff(c_8951, plain, (![D_811, B_812]: (~m1_subset_1(D_811, k1_zfmisc_1(u1_struct_0(B_812))) | ~l1_pre_topc(B_812))), inference(splitLeft, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_8958, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_8951])).
% 10.17/3.35  tff(c_8963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_8958])).
% 10.17/3.35  tff(c_8965, plain, (![C_813, A_814]: (v3_pre_topc(C_813, A_814) | k1_tops_1(A_814, C_813)!=C_813 | ~m1_subset_1(C_813, k1_zfmisc_1(u1_struct_0(A_814))) | ~l1_pre_topc(A_814) | ~v2_pre_topc(A_814))), inference(splitRight, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_8982, plain, (![A_815, A_816]: (v3_pre_topc(A_815, A_816) | k1_tops_1(A_816, A_815)!=A_815 | ~l1_pre_topc(A_816) | ~v2_pre_topc(A_816) | ~r1_tarski(A_815, u1_struct_0(A_816)))), inference(resolution, [status(thm)], [c_6, c_8965])).
% 10.17/3.35  tff(c_9009, plain, (![A_585]: (v3_pre_topc(A_585, '#skF_5') | k1_tops_1('#skF_5', A_585)!=A_585 | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_585, '#skF_7'))), inference(resolution, [status(thm)], [c_6753, c_8982])).
% 10.17/3.35  tff(c_9033, plain, (![A_817]: (v3_pre_topc(A_817, '#skF_5') | k1_tops_1('#skF_5', A_817)!=A_817 | ~r1_tarski(A_817, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_9009])).
% 10.17/3.35  tff(c_6739, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 10.17/3.35  tff(c_72, plain, (![D_102]: (~r2_hidden('#skF_6', D_102) | ~r1_tarski(D_102, '#skF_7') | ~v3_pre_topc(D_102, '#skF_5') | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0('#skF_5'))) | r1_tarski('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_8576, plain, (![D_728]: (~r2_hidden('#skF_6', D_728) | ~r1_tarski(D_728, '#skF_7') | ~v3_pre_topc(D_728, '#skF_5') | ~m1_subset_1(D_728, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_6739, c_72])).
% 10.17/3.35  tff(c_8598, plain, (![A_731]: (~r2_hidden('#skF_6', A_731) | ~r1_tarski(A_731, '#skF_7') | ~v3_pre_topc(A_731, '#skF_5') | ~r1_tarski(A_731, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_8576])).
% 10.17/3.35  tff(c_8610, plain, (![A_585]: (~r2_hidden('#skF_6', A_585) | ~v3_pre_topc(A_585, '#skF_5') | ~r1_tarski(A_585, '#skF_7'))), inference(resolution, [status(thm)], [c_6753, c_8598])).
% 10.17/3.35  tff(c_9041, plain, (![A_817]: (~r2_hidden('#skF_6', A_817) | k1_tops_1('#skF_5', A_817)!=A_817 | ~r1_tarski(A_817, '#skF_7'))), inference(resolution, [status(thm)], [c_9033, c_8610])).
% 10.17/3.35  tff(c_9958, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))!=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_9952, c_9041])).
% 10.17/3.35  tff(c_9976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_6738, c_6768, c_9188, c_9958])).
% 10.17/3.35  tff(c_9977, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 10.17/3.35  tff(c_10007, plain, (![A_861, B_862]: (r1_tarski(k1_tops_1(A_861, B_862), B_862) | ~m1_subset_1(B_862, k1_zfmisc_1(u1_struct_0(A_861))) | ~l1_pre_topc(A_861))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.35  tff(c_10012, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10007])).
% 10.17/3.35  tff(c_10016, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10012])).
% 10.17/3.35  tff(c_10037, plain, (![A_865, B_866]: (v3_pre_topc(k1_tops_1(A_865, B_866), A_865) | ~m1_subset_1(B_866, k1_zfmisc_1(u1_struct_0(A_865))) | ~l1_pre_topc(A_865) | ~v2_pre_topc(A_865))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/3.35  tff(c_10042, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10037])).
% 10.17/3.35  tff(c_10046, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_10042])).
% 10.17/3.35  tff(c_9980, plain, (![A_853, B_854]: (r1_tarski(A_853, B_854) | ~m1_subset_1(A_853, k1_zfmisc_1(B_854)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.17/3.35  tff(c_9988, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_9980])).
% 10.17/3.35  tff(c_9990, plain, (![A_855, C_856, B_857]: (r1_tarski(A_855, C_856) | ~r1_tarski(B_857, C_856) | ~r1_tarski(A_855, B_857))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.17/3.35  tff(c_9993, plain, (![A_855]: (r1_tarski(A_855, u1_struct_0('#skF_5')) | ~r1_tarski(A_855, '#skF_7'))), inference(resolution, [status(thm)], [c_9988, c_9990])).
% 10.17/3.35  tff(c_10470, plain, (![C_950, A_951]: (~m1_subset_1(C_950, k1_zfmisc_1(u1_struct_0(A_951))) | ~l1_pre_topc(A_951) | ~v2_pre_topc(A_951))), inference(splitLeft, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_10477, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10470])).
% 10.17/3.35  tff(c_10482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_10477])).
% 10.17/3.35  tff(c_10512, plain, (![B_957, D_958]: (k1_tops_1(B_957, D_958)=D_958 | ~v3_pre_topc(D_958, B_957) | ~m1_subset_1(D_958, k1_zfmisc_1(u1_struct_0(B_957))) | ~l1_pre_topc(B_957))), inference(splitRight, [status(thm)], [c_16])).
% 10.17/3.35  tff(c_10529, plain, (![B_959, A_960]: (k1_tops_1(B_959, A_960)=A_960 | ~v3_pre_topc(A_960, B_959) | ~l1_pre_topc(B_959) | ~r1_tarski(A_960, u1_struct_0(B_959)))), inference(resolution, [status(thm)], [c_6, c_10512])).
% 10.17/3.35  tff(c_10559, plain, (![A_855]: (k1_tops_1('#skF_5', A_855)=A_855 | ~v3_pre_topc(A_855, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_855, '#skF_7'))), inference(resolution, [status(thm)], [c_9993, c_10529])).
% 10.17/3.35  tff(c_10586, plain, (![A_961]: (k1_tops_1('#skF_5', A_961)=A_961 | ~v3_pre_topc(A_961, '#skF_5') | ~r1_tarski(A_961, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10559])).
% 10.17/3.35  tff(c_10604, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_10046, c_10586])).
% 10.17/3.35  tff(c_10617, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))=k1_tops_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10016, c_10604])).
% 10.17/3.35  tff(c_11835, plain, (![B_1002, A_1003, C_1004]: (r2_hidden(B_1002, k1_tops_1(A_1003, C_1004)) | ~m1_connsp_2(C_1004, A_1003, B_1002) | ~m1_subset_1(C_1004, k1_zfmisc_1(u1_struct_0(A_1003))) | ~m1_subset_1(B_1002, u1_struct_0(A_1003)) | ~l1_pre_topc(A_1003) | ~v2_pre_topc(A_1003) | v2_struct_0(A_1003))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.17/3.35  tff(c_11846, plain, (![B_1002]: (r2_hidden(B_1002, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_1002) | ~m1_subset_1(B_1002, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_11835])).
% 10.17/3.35  tff(c_11856, plain, (![B_1002]: (r2_hidden(B_1002, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_1002) | ~m1_subset_1(B_1002, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_11846])).
% 10.17/3.35  tff(c_11858, plain, (![B_1005]: (r2_hidden(B_1005, k1_tops_1('#skF_5', '#skF_7')) | ~m1_connsp_2('#skF_7', '#skF_5', B_1005) | ~m1_subset_1(B_1005, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_11856])).
% 10.17/3.35  tff(c_10387, plain, (![D_944, B_945]: (~m1_subset_1(D_944, k1_zfmisc_1(u1_struct_0(B_945))) | ~l1_pre_topc(B_945))), inference(splitLeft, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_10394, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_54, c_10387])).
% 10.17/3.35  tff(c_10399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_10394])).
% 10.17/3.35  tff(c_10401, plain, (![C_946, A_947]: (v3_pre_topc(C_946, A_947) | k1_tops_1(A_947, C_946)!=C_946 | ~m1_subset_1(C_946, k1_zfmisc_1(u1_struct_0(A_947))) | ~l1_pre_topc(A_947) | ~v2_pre_topc(A_947))), inference(splitRight, [status(thm)], [c_14])).
% 10.17/3.35  tff(c_10418, plain, (![A_948, A_949]: (v3_pre_topc(A_948, A_949) | k1_tops_1(A_949, A_948)!=A_948 | ~l1_pre_topc(A_949) | ~v2_pre_topc(A_949) | ~r1_tarski(A_948, u1_struct_0(A_949)))), inference(resolution, [status(thm)], [c_6, c_10401])).
% 10.17/3.35  tff(c_10445, plain, (![A_855]: (v3_pre_topc(A_855, '#skF_5') | k1_tops_1('#skF_5', A_855)!=A_855 | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski(A_855, '#skF_7'))), inference(resolution, [status(thm)], [c_9993, c_10418])).
% 10.17/3.35  tff(c_10484, plain, (![A_952]: (v3_pre_topc(A_952, '#skF_5') | k1_tops_1('#skF_5', A_952)!=A_952 | ~r1_tarski(A_952, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_10445])).
% 10.17/3.35  tff(c_9978, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 10.17/3.35  tff(c_68, plain, (![D_102]: (~r2_hidden('#skF_6', D_102) | ~r1_tarski(D_102, '#skF_7') | ~v3_pre_topc(D_102, '#skF_5') | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0('#skF_5'))) | r2_hidden('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.17/3.35  tff(c_10024, plain, (![D_863]: (~r2_hidden('#skF_6', D_863) | ~r1_tarski(D_863, '#skF_7') | ~v3_pre_topc(D_863, '#skF_5') | ~m1_subset_1(D_863, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_9978, c_68])).
% 10.17/3.35  tff(c_10059, plain, (![A_869]: (~r2_hidden('#skF_6', A_869) | ~r1_tarski(A_869, '#skF_7') | ~v3_pre_topc(A_869, '#skF_5') | ~r1_tarski(A_869, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_10024])).
% 10.17/3.35  tff(c_10071, plain, (![A_855]: (~r2_hidden('#skF_6', A_855) | ~v3_pre_topc(A_855, '#skF_5') | ~r1_tarski(A_855, '#skF_7'))), inference(resolution, [status(thm)], [c_9993, c_10059])).
% 10.17/3.35  tff(c_10491, plain, (![A_952]: (~r2_hidden('#skF_6', A_952) | k1_tops_1('#skF_5', A_952)!=A_952 | ~r1_tarski(A_952, '#skF_7'))), inference(resolution, [status(thm)], [c_10484, c_10071])).
% 10.17/3.35  tff(c_11868, plain, (k1_tops_1('#skF_5', k1_tops_1('#skF_5', '#skF_7'))!=k1_tops_1('#skF_5', '#skF_7') | ~r1_tarski(k1_tops_1('#skF_5', '#skF_7'), '#skF_7') | ~m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_11858, c_10491])).
% 10.17/3.35  tff(c_11889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_9977, c_10016, c_10617, c_11868])).
% 10.17/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.35  
% 10.17/3.35  Inference rules
% 10.17/3.35  ----------------------
% 10.17/3.35  #Ref     : 0
% 10.17/3.35  #Sup     : 2556
% 10.17/3.35  #Fact    : 0
% 10.17/3.35  #Define  : 0
% 10.17/3.35  #Split   : 49
% 10.17/3.35  #Chain   : 0
% 10.17/3.35  #Close   : 0
% 10.17/3.35  
% 10.17/3.35  Ordering : KBO
% 10.17/3.35  
% 10.17/3.35  Simplification rules
% 10.17/3.35  ----------------------
% 10.17/3.35  #Subsume      : 919
% 10.17/3.35  #Demod        : 2198
% 10.17/3.35  #Tautology    : 435
% 10.17/3.35  #SimpNegUnit  : 70
% 10.17/3.35  #BackRed      : 22
% 10.17/3.35  
% 10.17/3.35  #Partial instantiations: 0
% 10.17/3.35  #Strategies tried      : 1
% 10.17/3.35  
% 10.17/3.35  Timing (in seconds)
% 10.17/3.35  ----------------------
% 10.17/3.35  Preprocessing        : 0.34
% 10.17/3.35  Parsing              : 0.18
% 10.17/3.35  CNF conversion       : 0.03
% 10.17/3.36  Main loop            : 2.19
% 10.17/3.36  Inferencing          : 0.68
% 10.17/3.36  Reduction            : 0.61
% 10.17/3.36  Demodulation         : 0.41
% 10.17/3.36  BG Simplification    : 0.07
% 10.17/3.36  Subsumption          : 0.68
% 10.17/3.36  Abstraction          : 0.09
% 10.17/3.36  MUC search           : 0.00
% 10.17/3.36  Cooper               : 0.00
% 10.17/3.36  Total                : 2.60
% 10.17/3.36  Index Insertion      : 0.00
% 10.17/3.36  Index Deletion       : 0.00
% 10.17/3.36  Index Matching       : 0.00
% 10.17/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
