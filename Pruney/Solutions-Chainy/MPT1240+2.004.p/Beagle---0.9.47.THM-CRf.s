%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:45 EST 2020

% Result     : Theorem 8.90s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 403 expanded)
%              Number of leaves         :   33 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 (1193 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
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

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_9996,plain,(
    ! [A_641,C_642,B_643] :
      ( r1_tarski(A_641,C_642)
      | ~ r1_tarski(B_643,C_642)
      | ~ r1_tarski(A_641,B_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10003,plain,(
    ! [A_644] :
      ( r1_tarski(A_644,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_644,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9996])).

tff(c_9532,plain,(
    ! [A_580,C_581,B_582] :
      ( r1_tarski(A_580,C_581)
      | ~ r1_tarski(B_582,C_581)
      | ~ r1_tarski(A_580,B_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9537,plain,(
    ! [A_580] :
      ( r1_tarski(A_580,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_580,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9532])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9410,plain,(
    ! [A_570,B_571] :
      ( v3_pre_topc(k1_tops_1(A_570,B_571),A_570)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9420,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_9410])).

tff(c_9428,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_9420])).

tff(c_9258,plain,(
    ! [A_566,B_567] :
      ( r1_tarski(k1_tops_1(A_566,B_567),B_567)
      | ~ m1_subset_1(B_567,k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ l1_pre_topc(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9268,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_9258])).

tff(c_9276,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9268])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_92,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_8946,plain,(
    ! [A_532,C_533,B_534] :
      ( r1_tarski(A_532,C_533)
      | ~ r1_tarski(B_534,C_533)
      | ~ r1_tarski(A_532,B_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8967,plain,(
    ! [A_537] :
      ( r1_tarski(A_537,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_537,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_8946])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_96,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_90,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_66,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_98,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_114,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3',B_63)
      | ~ r1_tarski('#skF_5',B_63) ) ),
    inference(resolution,[status(thm)],[c_90,c_114])).

tff(c_48,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_3',D_50)
      | ~ r1_tarski(D_50,'#skF_4')
      | ~ v3_pre_topc(D_50,'#skF_2')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_489,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_497,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_119,c_489])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tops_1(A_86,B_87),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_331,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_326])).

tff(c_340,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_331])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_386,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_340,c_8])).

tff(c_498,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_36,plain,(
    ! [A_29,B_31] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_29),B_31),A_29)
      | ~ v3_pre_topc(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_500,plain,(
    ! [A_93,B_94] :
      ( k2_pre_topc(A_93,B_94) = B_94
      | ~ v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3561,plain,(
    ! [A_274,B_275] :
      ( k2_pre_topc(A_274,k3_subset_1(u1_struct_0(A_274),B_275)) = k3_subset_1(u1_struct_0(A_274),B_275)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_274),B_275),A_274)
      | ~ l1_pre_topc(A_274)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274))) ) ),
    inference(resolution,[status(thm)],[c_16,c_500])).

tff(c_7256,plain,(
    ! [A_408,B_409] :
      ( k2_pre_topc(A_408,k3_subset_1(u1_struct_0(A_408),B_409)) = k3_subset_1(u1_struct_0(A_408),B_409)
      | ~ v3_pre_topc(B_409,A_408)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408) ) ),
    inference(resolution,[status(thm)],[c_36,c_3561])).

tff(c_7263,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_7256])).

tff(c_7273,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_96,c_7263])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( k3_subset_1(u1_struct_0(A_22),k2_pre_topc(A_22,k3_subset_1(u1_struct_0(A_22),B_24))) = k1_tops_1(A_22,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7293,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7273,c_28])).

tff(c_7306,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_98,c_7293])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1076,plain,(
    ! [C_144,A_145,B_146] :
      ( r1_tarski(C_144,k3_subset_1(A_145,B_146))
      | ~ r1_tarski(B_146,k3_subset_1(A_145,C_144))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1088,plain,(
    ! [C_144,A_145] :
      ( r1_tarski(C_144,k3_subset_1(A_145,k3_subset_1(A_145,C_144)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(k3_subset_1(A_145,C_144),k1_zfmisc_1(A_145)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1076])).

tff(c_7357,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7306,c_1088])).

tff(c_7427,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7357])).

tff(c_7428,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_7427])).

tff(c_7447,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_7428])).

tff(c_7454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7447])).

tff(c_7455,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_8458,plain,(
    ! [A_504,B_505,C_506] :
      ( r1_tarski(k1_tops_1(A_504,B_505),k1_tops_1(A_504,C_506))
      | ~ r1_tarski(B_505,C_506)
      | ~ m1_subset_1(C_506,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ m1_subset_1(B_505,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ l1_pre_topc(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8490,plain,(
    ! [C_506] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_506))
      | ~ r1_tarski('#skF_5',C_506)
      | ~ m1_subset_1(C_506,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7455,c_8458])).

tff(c_8792,plain,(
    ! [C_521] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_521))
      | ~ r1_tarski('#skF_5',C_521)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_98,c_8490])).

tff(c_8810,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_8792])).

tff(c_8821,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8810])).

tff(c_8823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_8821])).

tff(c_8896,plain,(
    ! [D_526] :
      ( ~ r2_hidden('#skF_3',D_526)
      | ~ r1_tarski(D_526,'#skF_4')
      | ~ v3_pre_topc(D_526,'#skF_2')
      | ~ m1_subset_1(D_526,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8907,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_8896])).

tff(c_8922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_8907])).

tff(c_8924,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8928,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_8924])).

tff(c_8972,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8967,c_8928])).

tff(c_8979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8972])).

tff(c_8980,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_9040,plain,(
    ! [A_546,C_547,B_548] :
      ( r1_tarski(A_546,C_547)
      | ~ r1_tarski(B_548,C_547)
      | ~ r1_tarski(A_546,B_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9060,plain,(
    ! [A_550] :
      ( r1_tarski(A_550,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_550,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9040])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9069,plain,(
    ! [A_8,A_550] :
      ( r1_tarski(A_8,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_8,A_550)
      | ~ r1_tarski(A_550,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9060,c_14])).

tff(c_9278,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9276,c_9069])).

tff(c_9292,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9278])).

tff(c_8981,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_3',D_50)
      | ~ r1_tarski(D_50,'#skF_4')
      | ~ v3_pre_topc(D_50,'#skF_2')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9000,plain,(
    ! [D_540] :
      ( ~ r2_hidden('#skF_3',D_540)
      | ~ r1_tarski(D_540,'#skF_4')
      | ~ v3_pre_topc(D_540,'#skF_2')
      | ~ m1_subset_1(D_540,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8981,c_60])).

tff(c_9488,plain,(
    ! [A_577] :
      ( ~ r2_hidden('#skF_3',A_577)
      | ~ r1_tarski(A_577,'#skF_4')
      | ~ v3_pre_topc(A_577,'#skF_2')
      | ~ r1_tarski(A_577,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_9000])).

tff(c_9494,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_9292,c_9488])).

tff(c_9521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9428,c_9276,c_8980,c_9494])).

tff(c_9522,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9539,plain,(
    ! [C_583,B_584,A_585] :
      ( r2_hidden(C_583,B_584)
      | ~ r2_hidden(C_583,A_585)
      | ~ r1_tarski(A_585,B_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9560,plain,(
    ! [B_588] :
      ( r2_hidden('#skF_3',B_588)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_588) ) ),
    inference(resolution,[status(thm)],[c_9522,c_9539])).

tff(c_9569,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9537,c_9560])).

tff(c_9583,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_9569])).

tff(c_9599,plain,(
    ! [A_595,B_596] :
      ( r1_tarski(k1_tops_1(A_595,B_596),B_596)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9607,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_9599])).

tff(c_9612,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9607])).

tff(c_9614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9583,c_9612])).

tff(c_9616,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_9569])).

tff(c_9553,plain,(
    ! [A_587] :
      ( r1_tarski(A_587,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_587,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9532])).

tff(c_9732,plain,(
    ! [A_608,A_609] :
      ( r1_tarski(A_608,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_608,A_609)
      | ~ r1_tarski(A_609,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9553,c_14])).

tff(c_9736,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9616,c_9732])).

tff(c_9746,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9736])).

tff(c_9523,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_3',D_50)
      | ~ r1_tarski(D_50,'#skF_4')
      | ~ v3_pre_topc(D_50,'#skF_2')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9704,plain,(
    ! [D_606] :
      ( ~ r2_hidden('#skF_3',D_606)
      | ~ r1_tarski(D_606,'#skF_4')
      | ~ v3_pre_topc(D_606,'#skF_2')
      | ~ m1_subset_1(D_606,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9523,c_56])).

tff(c_9919,plain,(
    ! [A_631] :
      ( ~ r2_hidden('#skF_3',A_631)
      | ~ r1_tarski(A_631,'#skF_4')
      | ~ v3_pre_topc(A_631,'#skF_2')
      | ~ r1_tarski(A_631,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_9704])).

tff(c_9926,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_9746,c_9919])).

tff(c_9944,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9616,c_9522,c_9926])).

tff(c_9954,plain,(
    ! [A_633,B_634] :
      ( v3_pre_topc(k1_tops_1(A_633,B_634),A_633)
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9962,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_9954])).

tff(c_9967,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_9962])).

tff(c_9969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9944,c_9967])).

tff(c_9970,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_9982,plain,(
    ! [C_637,B_638,A_639] :
      ( r2_hidden(C_637,B_638)
      | ~ r2_hidden(C_637,A_639)
      | ~ r1_tarski(A_639,B_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9987,plain,(
    ! [B_638] :
      ( r2_hidden('#skF_3',B_638)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_638) ) ),
    inference(resolution,[status(thm)],[c_9970,c_9982])).

tff(c_10013,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10003,c_9987])).

tff(c_10015,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10013])).

tff(c_10063,plain,(
    ! [A_655,B_656] :
      ( r1_tarski(k1_tops_1(A_655,B_656),B_656)
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0(A_655)))
      | ~ l1_pre_topc(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_10071,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_10063])).

tff(c_10076,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10071])).

tff(c_10078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10015,c_10076])).

tff(c_10080,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_10013])).

tff(c_10165,plain,(
    ! [A_666,A_667] :
      ( r1_tarski(A_666,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_666,A_667)
      | ~ r1_tarski(A_667,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10003,c_14])).

tff(c_10169,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_10080,c_10165])).

tff(c_10179,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10169])).

tff(c_9971,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_50] :
      ( ~ r2_hidden('#skF_3',D_50)
      | ~ r1_tarski(D_50,'#skF_4')
      | ~ v3_pre_topc(D_50,'#skF_2')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_10388,plain,(
    ! [D_691] :
      ( ~ r2_hidden('#skF_3',D_691)
      | ~ r1_tarski(D_691,'#skF_4')
      | ~ v3_pre_topc(D_691,'#skF_2')
      | ~ m1_subset_1(D_691,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9971,c_52])).

tff(c_10407,plain,(
    ! [A_694] :
      ( ~ r2_hidden('#skF_3',A_694)
      | ~ r1_tarski(A_694,'#skF_4')
      | ~ v3_pre_topc(A_694,'#skF_2')
      | ~ r1_tarski(A_694,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_10388])).

tff(c_10417,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10179,c_10407])).

tff(c_10436,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10080,c_9970,c_10417])).

tff(c_10492,plain,(
    ! [A_700,B_701] :
      ( v3_pre_topc(k1_tops_1(A_700,B_701),A_700)
      | ~ m1_subset_1(B_701,k1_zfmisc_1(u1_struct_0(A_700)))
      | ~ l1_pre_topc(A_700)
      | ~ v2_pre_topc(A_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10502,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_10492])).

tff(c_10508,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_10502])).

tff(c_10510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10436,c_10508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n001.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 18:51:45 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.90/3.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.34  
% 9.21/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.34  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.21/3.34  
% 9.21/3.34  %Foreground sorts:
% 9.21/3.34  
% 9.21/3.34  
% 9.21/3.34  %Background operators:
% 9.21/3.34  
% 9.21/3.34  
% 9.21/3.34  %Foreground operators:
% 9.21/3.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.21/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.21/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.21/3.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.21/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.21/3.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.21/3.34  tff('#skF_5', type, '#skF_5': $i).
% 9.21/3.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.21/3.34  tff('#skF_2', type, '#skF_2': $i).
% 9.21/3.34  tff('#skF_3', type, '#skF_3': $i).
% 9.21/3.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.21/3.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.21/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.21/3.34  tff('#skF_4', type, '#skF_4': $i).
% 9.21/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.21/3.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.21/3.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.21/3.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.21/3.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.21/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.21/3.34  
% 9.21/3.37  tff(f_144, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 9.21/3.37  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.21/3.37  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.21/3.37  tff(f_97, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.21/3.37  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 9.21/3.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.21/3.37  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.21/3.37  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.21/3.37  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 9.21/3.37  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.21/3.37  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 9.21/3.37  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 9.21/3.37  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 9.21/3.37  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_70, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.21/3.37  tff(c_78, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 9.21/3.37  tff(c_9996, plain, (![A_641, C_642, B_643]: (r1_tarski(A_641, C_642) | ~r1_tarski(B_643, C_642) | ~r1_tarski(A_641, B_643))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.37  tff(c_10003, plain, (![A_644]: (r1_tarski(A_644, u1_struct_0('#skF_2')) | ~r1_tarski(A_644, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9996])).
% 9.21/3.37  tff(c_9532, plain, (![A_580, C_581, B_582]: (r1_tarski(A_580, C_581) | ~r1_tarski(B_582, C_581) | ~r1_tarski(A_580, B_582))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.37  tff(c_9537, plain, (![A_580]: (r1_tarski(A_580, u1_struct_0('#skF_2')) | ~r1_tarski(A_580, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9532])).
% 9.21/3.37  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_9410, plain, (![A_570, B_571]: (v3_pre_topc(k1_tops_1(A_570, B_571), A_570) | ~m1_subset_1(B_571, k1_zfmisc_1(u1_struct_0(A_570))) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.37  tff(c_9420, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_9410])).
% 9.21/3.37  tff(c_9428, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_9420])).
% 9.21/3.37  tff(c_9258, plain, (![A_566, B_567]: (r1_tarski(k1_tops_1(A_566, B_567), B_567) | ~m1_subset_1(B_567, k1_zfmisc_1(u1_struct_0(A_566))) | ~l1_pre_topc(A_566))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.21/3.37  tff(c_9268, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_9258])).
% 9.21/3.37  tff(c_9276, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9268])).
% 9.21/3.37  tff(c_58, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_92, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 9.21/3.37  tff(c_8946, plain, (![A_532, C_533, B_534]: (r1_tarski(A_532, C_533) | ~r1_tarski(B_534, C_533) | ~r1_tarski(A_532, B_534))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.37  tff(c_8967, plain, (![A_537]: (r1_tarski(A_537, u1_struct_0('#skF_2')) | ~r1_tarski(A_537, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_8946])).
% 9.21/3.37  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.21/3.37  tff(c_62, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_96, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 9.21/3.37  tff(c_54, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_90, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 9.21/3.37  tff(c_66, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_98, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_66])).
% 9.21/3.37  tff(c_114, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.37  tff(c_119, plain, (![B_63]: (r2_hidden('#skF_3', B_63) | ~r1_tarski('#skF_5', B_63))), inference(resolution, [status(thm)], [c_90, c_114])).
% 9.21/3.37  tff(c_48, plain, (![D_50]: (~r2_hidden('#skF_3', D_50) | ~r1_tarski(D_50, '#skF_4') | ~v3_pre_topc(D_50, '#skF_2') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_489, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 9.21/3.37  tff(c_497, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_119, c_489])).
% 9.21/3.37  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.21/3.37  tff(c_326, plain, (![A_86, B_87]: (r1_tarski(k1_tops_1(A_86, B_87), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.21/3.37  tff(c_331, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_98, c_326])).
% 9.21/3.37  tff(c_340, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_331])).
% 9.21/3.37  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.21/3.37  tff(c_386, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_340, c_8])).
% 9.21/3.37  tff(c_498, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_386])).
% 9.21/3.37  tff(c_36, plain, (![A_29, B_31]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_29), B_31), A_29) | ~v3_pre_topc(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.21/3.37  tff(c_500, plain, (![A_93, B_94]: (k2_pre_topc(A_93, B_94)=B_94 | ~v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.21/3.37  tff(c_3561, plain, (![A_274, B_275]: (k2_pre_topc(A_274, k3_subset_1(u1_struct_0(A_274), B_275))=k3_subset_1(u1_struct_0(A_274), B_275) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_274), B_275), A_274) | ~l1_pre_topc(A_274) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))))), inference(resolution, [status(thm)], [c_16, c_500])).
% 9.21/3.37  tff(c_7256, plain, (![A_408, B_409]: (k2_pre_topc(A_408, k3_subset_1(u1_struct_0(A_408), B_409))=k3_subset_1(u1_struct_0(A_408), B_409) | ~v3_pre_topc(B_409, A_408) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408))), inference(resolution, [status(thm)], [c_36, c_3561])).
% 9.21/3.37  tff(c_7263, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_98, c_7256])).
% 9.21/3.37  tff(c_7273, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_96, c_7263])).
% 9.21/3.37  tff(c_28, plain, (![A_22, B_24]: (k3_subset_1(u1_struct_0(A_22), k2_pre_topc(A_22, k3_subset_1(u1_struct_0(A_22), B_24)))=k1_tops_1(A_22, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.21/3.37  tff(c_7293, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7273, c_28])).
% 9.21/3.37  tff(c_7306, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_98, c_7293])).
% 9.21/3.37  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.21/3.37  tff(c_1076, plain, (![C_144, A_145, B_146]: (r1_tarski(C_144, k3_subset_1(A_145, B_146)) | ~r1_tarski(B_146, k3_subset_1(A_145, C_144)) | ~m1_subset_1(C_144, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.21/3.37  tff(c_1088, plain, (![C_144, A_145]: (r1_tarski(C_144, k3_subset_1(A_145, k3_subset_1(A_145, C_144))) | ~m1_subset_1(C_144, k1_zfmisc_1(A_145)) | ~m1_subset_1(k3_subset_1(A_145, C_144), k1_zfmisc_1(A_145)))), inference(resolution, [status(thm)], [c_12, c_1076])).
% 9.21/3.37  tff(c_7357, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7306, c_1088])).
% 9.21/3.37  tff(c_7427, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_7357])).
% 9.21/3.37  tff(c_7428, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_498, c_7427])).
% 9.21/3.37  tff(c_7447, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_7428])).
% 9.21/3.37  tff(c_7454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_7447])).
% 9.21/3.37  tff(c_7455, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_386])).
% 9.21/3.37  tff(c_8458, plain, (![A_504, B_505, C_506]: (r1_tarski(k1_tops_1(A_504, B_505), k1_tops_1(A_504, C_506)) | ~r1_tarski(B_505, C_506) | ~m1_subset_1(C_506, k1_zfmisc_1(u1_struct_0(A_504))) | ~m1_subset_1(B_505, k1_zfmisc_1(u1_struct_0(A_504))) | ~l1_pre_topc(A_504))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.21/3.37  tff(c_8490, plain, (![C_506]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_506)) | ~r1_tarski('#skF_5', C_506) | ~m1_subset_1(C_506, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7455, c_8458])).
% 9.21/3.37  tff(c_8792, plain, (![C_521]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_521)) | ~r1_tarski('#skF_5', C_521) | ~m1_subset_1(C_521, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_98, c_8490])).
% 9.21/3.37  tff(c_8810, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_8792])).
% 9.21/3.37  tff(c_8821, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8810])).
% 9.21/3.37  tff(c_8823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_8821])).
% 9.21/3.37  tff(c_8896, plain, (![D_526]: (~r2_hidden('#skF_3', D_526) | ~r1_tarski(D_526, '#skF_4') | ~v3_pre_topc(D_526, '#skF_2') | ~m1_subset_1(D_526, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 9.21/3.37  tff(c_8907, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_8896])).
% 9.21/3.37  tff(c_8922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_8907])).
% 9.21/3.37  tff(c_8924, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 9.21/3.37  tff(c_8928, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_8924])).
% 9.21/3.37  tff(c_8972, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8967, c_8928])).
% 9.21/3.37  tff(c_8979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_8972])).
% 9.21/3.37  tff(c_8980, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 9.21/3.37  tff(c_9040, plain, (![A_546, C_547, B_548]: (r1_tarski(A_546, C_547) | ~r1_tarski(B_548, C_547) | ~r1_tarski(A_546, B_548))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.37  tff(c_9060, plain, (![A_550]: (r1_tarski(A_550, u1_struct_0('#skF_2')) | ~r1_tarski(A_550, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9040])).
% 9.21/3.37  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.37  tff(c_9069, plain, (![A_8, A_550]: (r1_tarski(A_8, u1_struct_0('#skF_2')) | ~r1_tarski(A_8, A_550) | ~r1_tarski(A_550, '#skF_4'))), inference(resolution, [status(thm)], [c_9060, c_14])).
% 9.21/3.37  tff(c_9278, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_9276, c_9069])).
% 9.21/3.37  tff(c_9292, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9278])).
% 9.21/3.37  tff(c_8981, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 9.21/3.37  tff(c_60, plain, (![D_50]: (~r2_hidden('#skF_3', D_50) | ~r1_tarski(D_50, '#skF_4') | ~v3_pre_topc(D_50, '#skF_2') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_9000, plain, (![D_540]: (~r2_hidden('#skF_3', D_540) | ~r1_tarski(D_540, '#skF_4') | ~v3_pre_topc(D_540, '#skF_2') | ~m1_subset_1(D_540, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_8981, c_60])).
% 9.21/3.37  tff(c_9488, plain, (![A_577]: (~r2_hidden('#skF_3', A_577) | ~r1_tarski(A_577, '#skF_4') | ~v3_pre_topc(A_577, '#skF_2') | ~r1_tarski(A_577, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_9000])).
% 9.21/3.37  tff(c_9494, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_9292, c_9488])).
% 9.21/3.37  tff(c_9521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9428, c_9276, c_8980, c_9494])).
% 9.21/3.37  tff(c_9522, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 9.21/3.37  tff(c_9539, plain, (![C_583, B_584, A_585]: (r2_hidden(C_583, B_584) | ~r2_hidden(C_583, A_585) | ~r1_tarski(A_585, B_584))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.37  tff(c_9560, plain, (![B_588]: (r2_hidden('#skF_3', B_588) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_588))), inference(resolution, [status(thm)], [c_9522, c_9539])).
% 9.21/3.37  tff(c_9569, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9537, c_9560])).
% 9.21/3.37  tff(c_9583, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_9569])).
% 9.21/3.37  tff(c_9599, plain, (![A_595, B_596]: (r1_tarski(k1_tops_1(A_595, B_596), B_596) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.21/3.37  tff(c_9607, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_9599])).
% 9.21/3.37  tff(c_9612, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9607])).
% 9.21/3.37  tff(c_9614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9583, c_9612])).
% 9.21/3.37  tff(c_9616, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_9569])).
% 9.21/3.37  tff(c_9553, plain, (![A_587]: (r1_tarski(A_587, u1_struct_0('#skF_2')) | ~r1_tarski(A_587, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9532])).
% 9.21/3.37  tff(c_9732, plain, (![A_608, A_609]: (r1_tarski(A_608, u1_struct_0('#skF_2')) | ~r1_tarski(A_608, A_609) | ~r1_tarski(A_609, '#skF_4'))), inference(resolution, [status(thm)], [c_9553, c_14])).
% 9.21/3.37  tff(c_9736, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_9616, c_9732])).
% 9.21/3.37  tff(c_9746, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9736])).
% 9.21/3.37  tff(c_9523, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 9.21/3.37  tff(c_56, plain, (![D_50]: (~r2_hidden('#skF_3', D_50) | ~r1_tarski(D_50, '#skF_4') | ~v3_pre_topc(D_50, '#skF_2') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_9704, plain, (![D_606]: (~r2_hidden('#skF_3', D_606) | ~r1_tarski(D_606, '#skF_4') | ~v3_pre_topc(D_606, '#skF_2') | ~m1_subset_1(D_606, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_9523, c_56])).
% 9.21/3.37  tff(c_9919, plain, (![A_631]: (~r2_hidden('#skF_3', A_631) | ~r1_tarski(A_631, '#skF_4') | ~v3_pre_topc(A_631, '#skF_2') | ~r1_tarski(A_631, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_9704])).
% 9.21/3.37  tff(c_9926, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_9746, c_9919])).
% 9.21/3.37  tff(c_9944, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9616, c_9522, c_9926])).
% 9.21/3.37  tff(c_9954, plain, (![A_633, B_634]: (v3_pre_topc(k1_tops_1(A_633, B_634), A_633) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.37  tff(c_9962, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_9954])).
% 9.21/3.37  tff(c_9967, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_9962])).
% 9.21/3.37  tff(c_9969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9944, c_9967])).
% 9.21/3.37  tff(c_9970, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 9.21/3.37  tff(c_9982, plain, (![C_637, B_638, A_639]: (r2_hidden(C_637, B_638) | ~r2_hidden(C_637, A_639) | ~r1_tarski(A_639, B_638))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.37  tff(c_9987, plain, (![B_638]: (r2_hidden('#skF_3', B_638) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_638))), inference(resolution, [status(thm)], [c_9970, c_9982])).
% 9.21/3.37  tff(c_10013, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_10003, c_9987])).
% 9.21/3.37  tff(c_10015, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_10013])).
% 9.21/3.37  tff(c_10063, plain, (![A_655, B_656]: (r1_tarski(k1_tops_1(A_655, B_656), B_656) | ~m1_subset_1(B_656, k1_zfmisc_1(u1_struct_0(A_655))) | ~l1_pre_topc(A_655))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.21/3.37  tff(c_10071, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_10063])).
% 9.21/3.37  tff(c_10076, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10071])).
% 9.21/3.37  tff(c_10078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10015, c_10076])).
% 9.21/3.37  tff(c_10080, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_10013])).
% 9.21/3.37  tff(c_10165, plain, (![A_666, A_667]: (r1_tarski(A_666, u1_struct_0('#skF_2')) | ~r1_tarski(A_666, A_667) | ~r1_tarski(A_667, '#skF_4'))), inference(resolution, [status(thm)], [c_10003, c_14])).
% 9.21/3.37  tff(c_10169, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_10080, c_10165])).
% 9.21/3.37  tff(c_10179, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10169])).
% 9.21/3.37  tff(c_9971, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 9.21/3.37  tff(c_52, plain, (![D_50]: (~r2_hidden('#skF_3', D_50) | ~r1_tarski(D_50, '#skF_4') | ~v3_pre_topc(D_50, '#skF_2') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.21/3.37  tff(c_10388, plain, (![D_691]: (~r2_hidden('#skF_3', D_691) | ~r1_tarski(D_691, '#skF_4') | ~v3_pre_topc(D_691, '#skF_2') | ~m1_subset_1(D_691, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_9971, c_52])).
% 9.21/3.37  tff(c_10407, plain, (![A_694]: (~r2_hidden('#skF_3', A_694) | ~r1_tarski(A_694, '#skF_4') | ~v3_pre_topc(A_694, '#skF_2') | ~r1_tarski(A_694, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_10388])).
% 9.21/3.37  tff(c_10417, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_10179, c_10407])).
% 9.21/3.37  tff(c_10436, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10080, c_9970, c_10417])).
% 9.21/3.37  tff(c_10492, plain, (![A_700, B_701]: (v3_pre_topc(k1_tops_1(A_700, B_701), A_700) | ~m1_subset_1(B_701, k1_zfmisc_1(u1_struct_0(A_700))) | ~l1_pre_topc(A_700) | ~v2_pre_topc(A_700))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.21/3.37  tff(c_10502, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_10492])).
% 9.21/3.37  tff(c_10508, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_10502])).
% 9.21/3.37  tff(c_10510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10436, c_10508])).
% 9.21/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.37  
% 9.21/3.37  Inference rules
% 9.21/3.37  ----------------------
% 9.21/3.37  #Ref     : 0
% 9.21/3.37  #Sup     : 2416
% 9.21/3.37  #Fact    : 0
% 9.21/3.37  #Define  : 0
% 9.21/3.37  #Split   : 58
% 9.21/3.37  #Chain   : 0
% 9.21/3.37  #Close   : 0
% 9.21/3.37  
% 9.21/3.37  Ordering : KBO
% 9.21/3.37  
% 9.21/3.37  Simplification rules
% 9.21/3.37  ----------------------
% 9.21/3.37  #Subsume      : 795
% 9.21/3.37  #Demod        : 1031
% 9.21/3.37  #Tautology    : 395
% 9.21/3.37  #SimpNegUnit  : 45
% 9.21/3.37  #BackRed      : 4
% 9.21/3.37  
% 9.21/3.37  #Partial instantiations: 0
% 9.21/3.37  #Strategies tried      : 1
% 9.21/3.37  
% 9.21/3.37  Timing (in seconds)
% 9.21/3.37  ----------------------
% 9.21/3.37  Preprocessing        : 0.37
% 9.21/3.37  Parsing              : 0.21
% 9.21/3.37  CNF conversion       : 0.02
% 9.21/3.37  Main loop            : 2.10
% 9.21/3.37  Inferencing          : 0.58
% 9.21/3.37  Reduction            : 0.62
% 9.21/3.37  Demodulation         : 0.41
% 9.21/3.37  BG Simplification    : 0.06
% 9.21/3.37  Subsumption          : 0.69
% 9.21/3.37  Abstraction          : 0.07
% 9.21/3.37  MUC search           : 0.00
% 9.21/3.37  Cooper               : 0.00
% 9.21/3.37  Total                : 2.53
% 9.21/3.37  Index Insertion      : 0.00
% 9.21/3.37  Index Deletion       : 0.00
% 9.21/3.37  Index Matching       : 0.00
% 9.21/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
