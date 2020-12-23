%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:27 EST 2020

% Result     : Theorem 27.47s
% Output     : CNFRefutation 27.64s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 882 expanded)
%              Number of leaves         :   35 ( 310 expanded)
%              Depth                    :   22
%              Number of atoms          :  295 (2520 expanded)
%              Number of equality atoms :   39 ( 414 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => k1_tops_1(A,k2_tops_1(A,B)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(c_40,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_170,plain,(
    ! [A_62,B_63] :
      ( k1_tops_1(A_62,k1_tops_1(A_62,B_63)) = k1_tops_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_178,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_170])).

tff(c_184,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_178])).

tff(c_304,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,k2_pre_topc(A_69,k1_tops_1(A_69,B_68)))
      | ~ v4_tops_1(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_312,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_304])).

tff(c_317,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ v4_tops_1(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_312])).

tff(c_325,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_328,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_325])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_328])).

tff(c_334,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_58,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tops_1(A_44,B_45),B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_63,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_12,plain,(
    ! [A_7,B_11,C_13] :
      ( r1_tarski(k2_pre_topc(A_7,B_11),k2_pre_topc(A_7,C_13))
      | ~ r1_tarski(B_11,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( r1_tarski(B_16,k2_pre_topc(A_14,k1_tops_1(A_14,B_16)))
      | ~ v4_tops_1(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_pre_topc(A_5,k2_pre_topc(A_5,B_6)) = k2_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_340,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_334,c_10])).

tff(c_362,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_340])).

tff(c_120,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_pre_topc(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v3_pre_topc(k1_tops_1(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_131,plain,(
    ! [A_56,B_57] :
      ( v3_pre_topc(k1_tops_1(A_56,k2_pre_topc(A_56,B_57)),A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_120,c_24])).

tff(c_395,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_131])).

tff(c_410,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_395])).

tff(c_527,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_530,plain,
    ( ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_527])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334,c_530])).

tff(c_536,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_584,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(k2_pre_topc(A_86,B_87),k2_pre_topc(A_86,C_88))
      | ~ r1_tarski(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_592,plain,(
    ! [B_87] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_87),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(B_87,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_584])).

tff(c_21919,plain,(
    ! [B_232] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_232),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(B_232,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_536,c_592])).

tff(c_155,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,k2_pre_topc(A_60,B_61)) = k2_pre_topc(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_155])).

tff(c_169,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163])).

tff(c_30,plain,(
    ! [A_28,B_30] :
      ( r1_tarski(k1_tops_1(A_28,B_30),B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_203,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tops_1(A_64,k2_pre_topc(A_64,B_65)),k2_pre_topc(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_120,c_30])).

tff(c_211,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_203])).

tff(c_216,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_169,c_211])).

tff(c_217,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_220,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_217])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_220])).

tff(c_226,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_598,plain,(
    ! [B_87] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_87),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_87,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_584])).

tff(c_716,plain,(
    ! [B_94] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_94),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_94,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_226,c_598])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_725,plain,(
    ! [B_94] :
      ( k2_pre_topc('#skF_1',B_94) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',B_94))
      | ~ r1_tarski(B_94,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_716,c_2])).

tff(c_21936,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_21919,c_725])).

tff(c_22080,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_334,c_21936])).

tff(c_25731,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_22080])).

tff(c_25734,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_25731])).

tff(c_25738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_25734])).

tff(c_25740,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_22080])).

tff(c_607,plain,(
    ! [B_87] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_87),k2_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(B_87,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_226,c_598])).

tff(c_3106,plain,(
    ! [A_134,C_135,B_136] :
      ( k2_pre_topc(A_134,C_135) = k2_pre_topc(A_134,B_136)
      | ~ r1_tarski(k2_pre_topc(A_134,C_135),k2_pre_topc(A_134,B_136))
      | ~ r1_tarski(B_136,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_584,c_2])).

tff(c_3151,plain,(
    ! [B_87] :
      ( k2_pre_topc('#skF_1',B_87) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_87)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_87,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_607,c_3106])).

tff(c_5018,plain,(
    ! [B_156] :
      ( k2_pre_topc('#skF_1',B_156) = k2_pre_topc('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_156)
      | ~ r1_tarski(B_156,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_3151])).

tff(c_5051,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_536,c_5018])).

tff(c_5089,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_5051])).

tff(c_47755,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25740,c_5089])).

tff(c_47756,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_47755])).

tff(c_47997,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_47756])).

tff(c_48007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334,c_44,c_63,c_47997])).

tff(c_48008,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_47755])).

tff(c_480,plain,(
    ! [A_82,B_83] :
      ( k7_subset_1(u1_struct_0(A_82),k2_pre_topc(A_82,B_83),k1_tops_1(A_82,B_83)) = k2_tops_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_495,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_480])).

tff(c_506,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334,c_495])).

tff(c_48051,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48008,c_506])).

tff(c_26,plain,(
    ! [A_23,B_25] :
      ( k7_subset_1(u1_struct_0(A_23),k2_pre_topc(A_23,B_25),k1_tops_1(A_23,B_25)) = k2_tops_1(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48481,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48051,c_26])).

tff(c_48488,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_48481])).

tff(c_96,plain,(
    ! [A_52,B_53] :
      ( v3_pre_topc(k1_tops_1(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_96])).

tff(c_104,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_100])).

tff(c_38,plain,(
    ! [A_37,B_39] :
      ( v3_tops_1(k2_tops_1(A_37,B_39),A_37)
      | ~ v3_pre_topc(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_336,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_334,c_38])).

tff(c_356,plain,(
    v3_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_104,c_336])).

tff(c_105,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k2_tops_1(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [B_36,A_34] :
      ( v2_tops_1(B_36,A_34)
      | ~ v3_tops_1(B_36,A_34)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_784,plain,(
    ! [A_95,B_96] :
      ( v2_tops_1(k2_tops_1(A_95,B_96),A_95)
      | ~ v3_tops_1(k2_tops_1(A_95,B_96),A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_105,c_36])).

tff(c_786,plain,
    ( v2_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_356,c_784])).

tff(c_789,plain,(
    v2_tops_1(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334,c_786])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_135,plain,(
    ! [A_58,B_59] :
      ( k1_tops_1(A_58,B_59) = k1_xboole_0
      | ~ v2_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1091,plain,(
    ! [A_109,B_110] :
      ( k1_tops_1(A_109,k2_tops_1(A_109,B_110)) = k1_xboole_0
      | ~ v2_tops_1(k2_tops_1(A_109,B_110),A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_1095,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_789,c_1091])).

tff(c_1101,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334,c_1095])).

tff(c_48521,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48488,c_1101])).

tff(c_48537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_48521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.47/16.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.47/16.47  
% 27.47/16.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.47/16.47  %$ v4_tops_1 > v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 27.47/16.47  
% 27.47/16.47  %Foreground sorts:
% 27.47/16.47  
% 27.47/16.47  
% 27.47/16.47  %Background operators:
% 27.47/16.47  
% 27.47/16.47  
% 27.47/16.47  %Foreground operators:
% 27.47/16.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.47/16.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.47/16.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 27.47/16.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.47/16.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 27.47/16.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.47/16.47  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 27.47/16.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.47/16.47  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 27.47/16.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 27.47/16.47  tff('#skF_2', type, '#skF_2': $i).
% 27.47/16.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 27.47/16.47  tff('#skF_1', type, '#skF_1': $i).
% 27.47/16.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.47/16.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.47/16.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.47/16.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.47/16.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.47/16.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 27.47/16.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.47/16.47  
% 27.64/16.49  tff(f_147, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (k1_tops_1(A, k2_tops_1(A, B)) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 27.64/16.49  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 27.64/16.49  tff(f_99, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 27.64/16.49  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 27.64/16.49  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 27.64/16.49  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 27.64/16.49  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 27.64/16.49  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 27.64/16.49  tff(f_86, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 27.64/16.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.64/16.49  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 27.64/16.49  tff(f_135, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tops_1)).
% 27.64/16.49  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 27.64/16.49  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 27.64/16.49  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 27.64/16.49  tff(c_40, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.64/16.49  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.64/16.49  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.64/16.49  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 27.64/16.49  tff(c_170, plain, (![A_62, B_63]: (k1_tops_1(A_62, k1_tops_1(A_62, B_63))=k1_tops_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.64/16.49  tff(c_178, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_170])).
% 27.64/16.49  tff(c_184, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_178])).
% 27.64/16.49  tff(c_304, plain, (![B_68, A_69]: (r1_tarski(B_68, k2_pre_topc(A_69, k1_tops_1(A_69, B_68))) | ~v4_tops_1(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.64/16.49  tff(c_312, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_304])).
% 27.64/16.49  tff(c_317, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~v4_tops_1(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_312])).
% 27.64/16.49  tff(c_325, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_317])).
% 27.64/16.49  tff(c_328, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_325])).
% 27.64/16.49  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_328])).
% 27.64/16.49  tff(c_334, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_317])).
% 27.64/16.49  tff(c_58, plain, (![A_44, B_45]: (r1_tarski(k1_tops_1(A_44, B_45), B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.64/16.49  tff(c_60, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_58])).
% 27.64/16.49  tff(c_63, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 27.64/16.49  tff(c_12, plain, (![A_7, B_11, C_13]: (r1_tarski(k2_pre_topc(A_7, B_11), k2_pre_topc(A_7, C_13)) | ~r1_tarski(B_11, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.64/16.49  tff(c_42, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.64/16.49  tff(c_16, plain, (![B_16, A_14]: (r1_tarski(B_16, k2_pre_topc(A_14, k1_tops_1(A_14, B_16))) | ~v4_tops_1(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.64/16.49  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.64/16.49  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.64/16.49  tff(c_10, plain, (![A_5, B_6]: (k2_pre_topc(A_5, k2_pre_topc(A_5, B_6))=k2_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.64/16.49  tff(c_340, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_334, c_10])).
% 27.64/16.49  tff(c_362, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_340])).
% 27.64/16.49  tff(c_120, plain, (![A_56, B_57]: (m1_subset_1(k2_pre_topc(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.64/16.49  tff(c_24, plain, (![A_21, B_22]: (v3_pre_topc(k1_tops_1(A_21, B_22), A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.64/16.49  tff(c_131, plain, (![A_56, B_57]: (v3_pre_topc(k1_tops_1(A_56, k2_pre_topc(A_56, B_57)), A_56) | ~v2_pre_topc(A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_120, c_24])).
% 27.64/16.49  tff(c_395, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_362, c_131])).
% 27.64/16.49  tff(c_410, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_395])).
% 27.64/16.49  tff(c_527, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_410])).
% 27.64/16.49  tff(c_530, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_527])).
% 27.64/16.49  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_334, c_530])).
% 27.64/16.49  tff(c_536, plain, (m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_410])).
% 27.64/16.49  tff(c_584, plain, (![A_86, B_87, C_88]: (r1_tarski(k2_pre_topc(A_86, B_87), k2_pre_topc(A_86, C_88)) | ~r1_tarski(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.64/16.49  tff(c_592, plain, (![B_87]: (r1_tarski(k2_pre_topc('#skF_1', B_87), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(B_87, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_584])).
% 27.64/16.49  tff(c_21919, plain, (![B_232]: (r1_tarski(k2_pre_topc('#skF_1', B_232), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(B_232, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_536, c_592])).
% 27.64/16.49  tff(c_155, plain, (![A_60, B_61]: (k2_pre_topc(A_60, k2_pre_topc(A_60, B_61))=k2_pre_topc(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.64/16.49  tff(c_163, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_155])).
% 27.64/16.49  tff(c_169, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163])).
% 27.64/16.49  tff(c_30, plain, (![A_28, B_30]: (r1_tarski(k1_tops_1(A_28, B_30), B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.64/16.49  tff(c_203, plain, (![A_64, B_65]: (r1_tarski(k1_tops_1(A_64, k2_pre_topc(A_64, B_65)), k2_pre_topc(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_120, c_30])).
% 27.64/16.49  tff(c_211, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_203])).
% 27.64/16.49  tff(c_216, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_169, c_211])).
% 27.64/16.49  tff(c_217, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_216])).
% 27.64/16.49  tff(c_220, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_217])).
% 27.64/16.49  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_220])).
% 27.64/16.49  tff(c_226, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_216])).
% 27.64/16.49  tff(c_598, plain, (![B_87]: (r1_tarski(k2_pre_topc('#skF_1', B_87), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_87, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_584])).
% 27.64/16.49  tff(c_716, plain, (![B_94]: (r1_tarski(k2_pre_topc('#skF_1', B_94), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_94, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_226, c_598])).
% 27.64/16.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.64/16.49  tff(c_725, plain, (![B_94]: (k2_pre_topc('#skF_1', B_94)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', B_94)) | ~r1_tarski(B_94, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_716, c_2])).
% 27.64/16.49  tff(c_21936, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_21919, c_725])).
% 27.64/16.49  tff(c_22080, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_334, c_21936])).
% 27.64/16.49  tff(c_25731, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_22080])).
% 27.64/16.49  tff(c_25734, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_25731])).
% 27.64/16.49  tff(c_25738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_25734])).
% 27.64/16.49  tff(c_25740, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_22080])).
% 27.64/16.49  tff(c_607, plain, (![B_87]: (r1_tarski(k2_pre_topc('#skF_1', B_87), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(B_87, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_226, c_598])).
% 27.64/16.50  tff(c_3106, plain, (![A_134, C_135, B_136]: (k2_pre_topc(A_134, C_135)=k2_pre_topc(A_134, B_136) | ~r1_tarski(k2_pre_topc(A_134, C_135), k2_pre_topc(A_134, B_136)) | ~r1_tarski(B_136, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_584, c_2])).
% 27.64/16.50  tff(c_3151, plain, (![B_87]: (k2_pre_topc('#skF_1', B_87)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_87) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_87, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_607, c_3106])).
% 27.64/16.50  tff(c_5018, plain, (![B_156]: (k2_pre_topc('#skF_1', B_156)=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_156) | ~r1_tarski(B_156, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_3151])).
% 27.64/16.50  tff(c_5051, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_536, c_5018])).
% 27.64/16.50  tff(c_5089, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_5051])).
% 27.64/16.50  tff(c_47755, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_25740, c_5089])).
% 27.64/16.50  tff(c_47756, plain, (~r1_tarski(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_47755])).
% 27.64/16.50  tff(c_47997, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_47756])).
% 27.64/16.50  tff(c_48007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_334, c_44, c_63, c_47997])).
% 27.64/16.50  tff(c_48008, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_47755])).
% 27.64/16.50  tff(c_480, plain, (![A_82, B_83]: (k7_subset_1(u1_struct_0(A_82), k2_pre_topc(A_82, B_83), k1_tops_1(A_82, B_83))=k2_tops_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_93])).
% 27.64/16.50  tff(c_495, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_184, c_480])).
% 27.64/16.50  tff(c_506, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_334, c_495])).
% 27.64/16.50  tff(c_48051, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48008, c_506])).
% 27.64/16.50  tff(c_26, plain, (![A_23, B_25]: (k7_subset_1(u1_struct_0(A_23), k2_pre_topc(A_23, B_25), k1_tops_1(A_23, B_25))=k2_tops_1(A_23, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 27.64/16.50  tff(c_48481, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48051, c_26])).
% 27.64/16.50  tff(c_48488, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_48481])).
% 27.64/16.50  tff(c_96, plain, (![A_52, B_53]: (v3_pre_topc(k1_tops_1(A_52, B_53), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.64/16.50  tff(c_100, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_96])).
% 27.64/16.50  tff(c_104, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_100])).
% 27.64/16.50  tff(c_38, plain, (![A_37, B_39]: (v3_tops_1(k2_tops_1(A_37, B_39), A_37) | ~v3_pre_topc(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_135])).
% 27.64/16.50  tff(c_336, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_334, c_38])).
% 27.64/16.50  tff(c_356, plain, (v3_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_104, c_336])).
% 27.64/16.50  tff(c_105, plain, (![A_54, B_55]: (m1_subset_1(k2_tops_1(A_54, B_55), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.64/16.50  tff(c_36, plain, (![B_36, A_34]: (v2_tops_1(B_36, A_34) | ~v3_tops_1(B_36, A_34) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_124])).
% 27.64/16.50  tff(c_784, plain, (![A_95, B_96]: (v2_tops_1(k2_tops_1(A_95, B_96), A_95) | ~v3_tops_1(k2_tops_1(A_95, B_96), A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_105, c_36])).
% 27.64/16.50  tff(c_786, plain, (v2_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_356, c_784])).
% 27.64/16.50  tff(c_789, plain, (v2_tops_1(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_334, c_786])).
% 27.64/16.50  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.64/16.50  tff(c_135, plain, (![A_58, B_59]: (k1_tops_1(A_58, B_59)=k1_xboole_0 | ~v2_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_115])).
% 27.64/16.50  tff(c_1091, plain, (![A_109, B_110]: (k1_tops_1(A_109, k2_tops_1(A_109, B_110))=k1_xboole_0 | ~v2_tops_1(k2_tops_1(A_109, B_110), A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_22, c_135])).
% 27.64/16.50  tff(c_1095, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_789, c_1091])).
% 27.64/16.50  tff(c_1101, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_334, c_1095])).
% 27.64/16.50  tff(c_48521, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48488, c_1101])).
% 27.64/16.50  tff(c_48537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_48521])).
% 27.64/16.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.64/16.50  
% 27.64/16.50  Inference rules
% 27.64/16.50  ----------------------
% 27.64/16.50  #Ref     : 0
% 27.64/16.50  #Sup     : 10583
% 27.64/16.50  #Fact    : 0
% 27.64/16.50  #Define  : 0
% 27.64/16.50  #Split   : 242
% 27.64/16.50  #Chain   : 0
% 27.64/16.50  #Close   : 0
% 27.64/16.50  
% 27.64/16.50  Ordering : KBO
% 27.64/16.50  
% 27.64/16.50  Simplification rules
% 27.64/16.50  ----------------------
% 27.64/16.50  #Subsume      : 1640
% 27.64/16.50  #Demod        : 38594
% 27.64/16.50  #Tautology    : 3218
% 27.64/16.50  #SimpNegUnit  : 549
% 27.64/16.50  #BackRed      : 157
% 27.64/16.50  
% 27.64/16.50  #Partial instantiations: 0
% 27.64/16.50  #Strategies tried      : 1
% 27.64/16.50  
% 27.64/16.50  Timing (in seconds)
% 27.64/16.50  ----------------------
% 27.64/16.50  Preprocessing        : 0.31
% 27.64/16.50  Parsing              : 0.17
% 27.64/16.50  CNF conversion       : 0.02
% 27.64/16.50  Main loop            : 15.35
% 27.64/16.50  Inferencing          : 1.68
% 27.64/16.50  Reduction            : 9.57
% 27.64/16.50  Demodulation         : 8.31
% 27.64/16.50  BG Simplification    : 0.20
% 27.64/16.50  Subsumption          : 3.42
% 27.64/16.50  Abstraction          : 0.36
% 27.64/16.50  MUC search           : 0.00
% 27.64/16.50  Cooper               : 0.00
% 27.64/16.50  Total                : 15.71
% 27.64/16.50  Index Insertion      : 0.00
% 27.64/16.50  Index Deletion       : 0.00
% 27.64/16.50  Index Matching       : 0.00
% 27.64/16.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
