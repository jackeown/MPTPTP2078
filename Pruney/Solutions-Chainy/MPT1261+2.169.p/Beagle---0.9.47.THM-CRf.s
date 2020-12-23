%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 179 expanded)
%              Number of leaves         :   38 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 361 expanded)
%              Number of equality atoms :   63 ( 113 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4845,plain,(
    ! [A_233,B_234,C_235] :
      ( k7_subset_1(A_233,B_234,C_235) = k4_xboole_0(B_234,C_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4851,plain,(
    ! [C_235] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_235) = k4_xboole_0('#skF_2',C_235) ),
    inference(resolution,[status(thm)],[c_38,c_4845])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1345,plain,(
    ! [B_106,A_107] :
      ( v4_pre_topc(B_106,A_107)
      | k2_pre_topc(A_107,B_106) != B_106
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1355,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1345])).

tff(c_1360,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1355])).

tff(c_1361,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1360])).

tff(c_1604,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_116),B_117,k2_tops_1(A_116,B_117)) = k2_pre_topc(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1611,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1604])).

tff(c_1616,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1611])).

tff(c_485,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_subset_1(A_67,B_68,C_69) = k4_xboole_0(B_68,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_548,plain,(
    ! [C_70] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_70) = k4_xboole_0('#skF_2',C_70) ),
    inference(resolution,[status(thm)],[c_38,c_485])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_153,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_50])).

tff(c_554,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_153])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_213,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_213])).

tff(c_238,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_225])).

tff(c_568,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_238])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_tops_1(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_883,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4297,plain,(
    ! [A_206,B_207,B_208] :
      ( k4_subset_1(u1_struct_0(A_206),B_207,k2_tops_1(A_206,B_208)) = k2_xboole_0(B_207,k2_tops_1(A_206,B_208))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_30,c_883])).

tff(c_4304,plain,(
    ! [B_208] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_208)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_4297])).

tff(c_4391,plain,(
    ! [B_209] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_209)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_209))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4304])).

tff(c_4402,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_4391])).

tff(c_4408,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_568,c_4402])).

tff(c_4410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1361,c_4408])).

tff(c_4411,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4893,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4851,c_4411])).

tff(c_4412,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5500,plain,(
    ! [A_267,B_268] :
      ( r1_tarski(k2_tops_1(A_267,B_268),B_268)
      | ~ v4_pre_topc(B_268,A_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5507,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_5500])).

tff(c_5512,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4412,c_5507])).

tff(c_6164,plain,(
    ! [A_290,B_291] :
      ( k7_subset_1(u1_struct_0(A_290),B_291,k2_tops_1(A_290,B_291)) = k1_tops_1(A_290,B_291)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ l1_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6171,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_6164])).

tff(c_6176,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4851,c_6171])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5523,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5512,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4639,plain,(
    ! [A_225,B_226] :
      ( k4_xboole_0(A_225,B_226) = k3_subset_1(A_225,B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4780,plain,(
    ! [B_231,A_232] :
      ( k4_xboole_0(B_231,A_232) = k3_subset_1(B_231,A_232)
      | ~ r1_tarski(A_232,B_231) ) ),
    inference(resolution,[status(thm)],[c_24,c_4639])).

tff(c_7119,plain,(
    ! [B_324,A_325] :
      ( k4_xboole_0(B_324,A_325) = k3_subset_1(B_324,A_325)
      | k4_xboole_0(A_325,B_324) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_4780])).

tff(c_7131,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5523,c_7119])).

tff(c_7156,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_7131])).

tff(c_4702,plain,(
    ! [A_227,B_228] :
      ( k3_subset_1(A_227,k3_subset_1(A_227,B_228)) = B_228
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4707,plain,(
    ! [B_21,A_20] :
      ( k3_subset_1(B_21,k3_subset_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_4702])).

tff(c_7610,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7156,c_4707])).

tff(c_7614,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5512,c_7610])).

tff(c_4413,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(A_210,B_211) = k1_xboole_0
      | ~ r1_tarski(A_210,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4425,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4413])).

tff(c_6216,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6176,c_4425])).

tff(c_7151,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6216,c_7119])).

tff(c_8146,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7614,c_7151])).

tff(c_8147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4893,c_8146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.40  
% 6.92/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.40  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.95/2.40  
% 6.95/2.40  %Foreground sorts:
% 6.95/2.40  
% 6.95/2.40  
% 6.95/2.40  %Background operators:
% 6.95/2.40  
% 6.95/2.40  
% 6.95/2.40  %Foreground operators:
% 6.95/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.95/2.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.95/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.95/2.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.95/2.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.95/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.95/2.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.95/2.40  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.95/2.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.95/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.95/2.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.95/2.40  tff('#skF_1', type, '#skF_1': $i).
% 6.95/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.95/2.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.95/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.95/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.95/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.95/2.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.95/2.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.95/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.95/2.40  
% 6.95/2.42  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 6.95/2.42  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.95/2.42  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.95/2.42  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.95/2.42  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.95/2.42  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.95/2.42  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.95/2.42  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.95/2.42  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.95/2.42  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.95/2.42  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 6.95/2.42  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 6.95/2.42  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.95/2.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.95/2.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.95/2.42  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.95/2.42  tff(c_4845, plain, (![A_233, B_234, C_235]: (k7_subset_1(A_233, B_234, C_235)=k4_xboole_0(B_234, C_235) | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.95/2.42  tff(c_4851, plain, (![C_235]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_235)=k4_xboole_0('#skF_2', C_235))), inference(resolution, [status(thm)], [c_38, c_4845])).
% 6.95/2.42  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.95/2.42  tff(c_72, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 6.95/2.42  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.95/2.42  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.95/2.42  tff(c_1345, plain, (![B_106, A_107]: (v4_pre_topc(B_106, A_107) | k2_pre_topc(A_107, B_106)!=B_106 | ~v2_pre_topc(A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.95/2.42  tff(c_1355, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1345])).
% 6.95/2.42  tff(c_1360, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1355])).
% 6.95/2.42  tff(c_1361, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_72, c_1360])).
% 6.95/2.42  tff(c_1604, plain, (![A_116, B_117]: (k4_subset_1(u1_struct_0(A_116), B_117, k2_tops_1(A_116, B_117))=k2_pre_topc(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.95/2.42  tff(c_1611, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1604])).
% 6.95/2.42  tff(c_1616, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1611])).
% 6.95/2.42  tff(c_485, plain, (![A_67, B_68, C_69]: (k7_subset_1(A_67, B_68, C_69)=k4_xboole_0(B_68, C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.95/2.42  tff(c_548, plain, (![C_70]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_70)=k4_xboole_0('#skF_2', C_70))), inference(resolution, [status(thm)], [c_38, c_485])).
% 6.95/2.42  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.95/2.42  tff(c_153, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_50])).
% 6.95/2.42  tff(c_554, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_548, c_153])).
% 6.95/2.42  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.42  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.95/2.42  tff(c_73, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.42  tff(c_85, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_73])).
% 6.95/2.42  tff(c_213, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.95/2.42  tff(c_225, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_85, c_213])).
% 6.95/2.42  tff(c_238, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_225])).
% 6.95/2.42  tff(c_568, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_554, c_238])).
% 6.95/2.42  tff(c_30, plain, (![A_25, B_26]: (m1_subset_1(k2_tops_1(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.95/2.42  tff(c_883, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.95/2.42  tff(c_4297, plain, (![A_206, B_207, B_208]: (k4_subset_1(u1_struct_0(A_206), B_207, k2_tops_1(A_206, B_208))=k2_xboole_0(B_207, k2_tops_1(A_206, B_208)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_30, c_883])).
% 6.95/2.42  tff(c_4304, plain, (![B_208]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_208))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_4297])).
% 6.95/2.42  tff(c_4391, plain, (![B_209]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_209))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_209)) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4304])).
% 6.95/2.42  tff(c_4402, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_4391])).
% 6.95/2.42  tff(c_4408, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_568, c_4402])).
% 6.95/2.42  tff(c_4410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1361, c_4408])).
% 6.95/2.42  tff(c_4411, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.95/2.42  tff(c_4893, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4851, c_4411])).
% 6.95/2.42  tff(c_4412, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 6.95/2.42  tff(c_5500, plain, (![A_267, B_268]: (r1_tarski(k2_tops_1(A_267, B_268), B_268) | ~v4_pre_topc(B_268, A_267) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.95/2.42  tff(c_5507, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_5500])).
% 6.95/2.42  tff(c_5512, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4412, c_5507])).
% 6.95/2.42  tff(c_6164, plain, (![A_290, B_291]: (k7_subset_1(u1_struct_0(A_290), B_291, k2_tops_1(A_290, B_291))=k1_tops_1(A_290, B_291) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_290))) | ~l1_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.95/2.42  tff(c_6171, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_6164])).
% 6.95/2.42  tff(c_6176, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4851, c_6171])).
% 6.95/2.42  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.42  tff(c_5523, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_5512, c_4])).
% 6.95/2.42  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.42  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.95/2.42  tff(c_4639, plain, (![A_225, B_226]: (k4_xboole_0(A_225, B_226)=k3_subset_1(A_225, B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.95/2.42  tff(c_4780, plain, (![B_231, A_232]: (k4_xboole_0(B_231, A_232)=k3_subset_1(B_231, A_232) | ~r1_tarski(A_232, B_231))), inference(resolution, [status(thm)], [c_24, c_4639])).
% 6.95/2.42  tff(c_7119, plain, (![B_324, A_325]: (k4_xboole_0(B_324, A_325)=k3_subset_1(B_324, A_325) | k4_xboole_0(A_325, B_324)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_4780])).
% 6.95/2.42  tff(c_7131, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5523, c_7119])).
% 6.95/2.42  tff(c_7156, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6176, c_7131])).
% 6.95/2.42  tff(c_4702, plain, (![A_227, B_228]: (k3_subset_1(A_227, k3_subset_1(A_227, B_228))=B_228 | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.95/2.42  tff(c_4707, plain, (![B_21, A_20]: (k3_subset_1(B_21, k3_subset_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_24, c_4702])).
% 6.95/2.42  tff(c_7610, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7156, c_4707])).
% 6.95/2.42  tff(c_7614, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5512, c_7610])).
% 6.95/2.42  tff(c_4413, plain, (![A_210, B_211]: (k4_xboole_0(A_210, B_211)=k1_xboole_0 | ~r1_tarski(A_210, B_211))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.95/2.42  tff(c_4425, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_4413])).
% 6.95/2.42  tff(c_6216, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6176, c_4425])).
% 6.95/2.42  tff(c_7151, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6216, c_7119])).
% 6.95/2.42  tff(c_8146, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7614, c_7151])).
% 6.95/2.42  tff(c_8147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4893, c_8146])).
% 6.95/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.42  
% 6.95/2.42  Inference rules
% 6.95/2.42  ----------------------
% 6.95/2.42  #Ref     : 0
% 6.95/2.42  #Sup     : 2091
% 6.95/2.42  #Fact    : 0
% 6.95/2.42  #Define  : 0
% 6.95/2.42  #Split   : 8
% 6.95/2.42  #Chain   : 0
% 6.95/2.42  #Close   : 0
% 6.95/2.42  
% 6.95/2.42  Ordering : KBO
% 6.95/2.42  
% 6.95/2.42  Simplification rules
% 6.95/2.42  ----------------------
% 6.95/2.42  #Subsume      : 7
% 6.95/2.42  #Demod        : 1719
% 6.95/2.42  #Tautology    : 1400
% 6.95/2.42  #SimpNegUnit  : 10
% 6.95/2.42  #BackRed      : 24
% 6.95/2.42  
% 6.95/2.42  #Partial instantiations: 0
% 6.95/2.42  #Strategies tried      : 1
% 6.95/2.42  
% 6.95/2.42  Timing (in seconds)
% 6.95/2.42  ----------------------
% 6.95/2.42  Preprocessing        : 0.33
% 6.95/2.42  Parsing              : 0.18
% 6.95/2.42  CNF conversion       : 0.02
% 6.95/2.42  Main loop            : 1.29
% 6.95/2.42  Inferencing          : 0.41
% 6.95/2.42  Reduction            : 0.51
% 6.95/2.42  Demodulation         : 0.39
% 6.95/2.42  BG Simplification    : 0.04
% 6.95/2.42  Subsumption          : 0.22
% 6.95/2.42  Abstraction          : 0.06
% 6.95/2.42  MUC search           : 0.00
% 6.95/2.42  Cooper               : 0.00
% 6.95/2.42  Total                : 1.66
% 6.95/2.42  Index Insertion      : 0.00
% 6.95/2.42  Index Deletion       : 0.00
% 6.95/2.42  Index Matching       : 0.00
% 6.95/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
