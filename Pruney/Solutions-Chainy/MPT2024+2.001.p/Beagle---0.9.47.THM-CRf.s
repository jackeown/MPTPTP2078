%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 488 expanded)
%              Number of leaves         :   33 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 (1849 expanded)
%              Number of equality atoms :   14 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_729,plain,(
    ! [A_101,B_102,C_103] :
      ( '#skF_1'(A_101,B_102,C_103) = C_103
      | ~ m1_subset_1(C_103,u1_struct_0(k9_yellow_6(A_101,B_102)))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_735,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_729])).

tff(c_742,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_735])).

tff(c_743,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_742])).

tff(c_753,plain,(
    ! [B_104,A_105,C_106] :
      ( r2_hidden(B_104,'#skF_1'(A_105,B_104,C_106))
      | ~ m1_subset_1(C_106,u1_struct_0(k9_yellow_6(A_105,B_104)))
      | ~ m1_subset_1(B_104,u1_struct_0(A_105))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_757,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_753])).

tff(c_764,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_743,c_757])).

tff(c_765,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_764])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ v1_xboole_0(C_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(C_79))
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_209,plain,(
    ! [B_15,A_81,A_14] :
      ( ~ v1_xboole_0(B_15)
      | ~ r2_hidden(A_81,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_821,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(B_112)
      | ~ r1_tarski('#skF_4',B_112) ) ),
    inference(resolution,[status(thm)],[c_765,c_209])).

tff(c_831,plain,(
    ! [B_6] : ~ v1_xboole_0(k2_xboole_0('#skF_4',B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_821])).

tff(c_53,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_62,B_61] : r1_tarski(A_62,k2_xboole_0(B_61,A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_732,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_729])).

tff(c_738,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_732])).

tff(c_739,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_738])).

tff(c_755,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_753])).

tff(c_760,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_739,c_755])).

tff(c_761,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_760])).

tff(c_498,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_906,plain,(
    ! [A_119,B_120,A_121] :
      ( m1_subset_1(A_119,B_120)
      | ~ r2_hidden(A_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(resolution,[status(thm)],[c_16,c_498])).

tff(c_1049,plain,(
    ! [B_131] :
      ( m1_subset_1('#skF_3',B_131)
      | ~ r1_tarski('#skF_5',B_131) ) ),
    inference(resolution,[status(thm)],[c_761,c_906])).

tff(c_1063,plain,(
    ! [B_61] : m1_subset_1('#skF_3',k2_xboole_0(B_61,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_1049])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_927,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_subset_1('#skF_1'(A_123,B_124,C_125),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(C_125,u1_struct_0(k9_yellow_6(A_123,B_124)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_937,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_927])).

tff(c_945,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_937])).

tff(c_946,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_945])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_959,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_946,c_14])).

tff(c_940,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_927])).

tff(c_948,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_940])).

tff(c_949,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_948])).

tff(c_982,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_949,c_14])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_990,plain,(
    k2_xboole_0('#skF_5',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_982,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_282,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(k2_xboole_0(A_87,C_88),k2_xboole_0(B_89,C_88))
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1380,plain,(
    ! [A_143,B_144,A_145] :
      ( r1_tarski(k2_xboole_0(A_143,B_144),k2_xboole_0(B_144,A_145))
      | ~ r1_tarski(A_143,A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_282])).

tff(c_4204,plain,(
    ! [A_210] :
      ( r1_tarski(k2_xboole_0(A_210,'#skF_5'),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_210,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_1380])).

tff(c_791,plain,(
    ! [A_108,B_109,C_110] :
      ( v3_pre_topc('#skF_1'(A_108,B_109,C_110),A_108)
      | ~ m1_subset_1(C_110,u1_struct_0(k9_yellow_6(A_108,B_109)))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_793,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_791])).

tff(c_798,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_739,c_793])).

tff(c_799,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_798])).

tff(c_795,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_791])).

tff(c_802,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_743,c_795])).

tff(c_803,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_802])).

tff(c_1116,plain,(
    ! [B_134,C_135,A_136] :
      ( v3_pre_topc(k2_xboole_0(B_134,C_135),A_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v3_pre_topc(C_135,A_136)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v3_pre_topc(B_134,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1120,plain,(
    ! [B_134] :
      ( v3_pre_topc(k2_xboole_0(B_134,'#skF_4'),'#skF_2')
      | ~ v3_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_134,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_946,c_1116])).

tff(c_1351,plain,(
    ! [B_142] :
      ( v3_pre_topc(k2_xboole_0(B_142,'#skF_4'),'#skF_2')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_142,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_803,c_1120])).

tff(c_1354,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_5','#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_949,c_1351])).

tff(c_1368,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_2,c_1354])).

tff(c_1329,plain,(
    ! [C_139,A_140,B_141] :
      ( r2_hidden(C_139,u1_struct_0(k9_yellow_6(A_140,B_141)))
      | ~ v3_pre_topc(C_139,A_140)
      | ~ r2_hidden(B_141,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4083,plain,(
    ! [C_200,A_201,B_202] :
      ( m1_subset_1(C_200,u1_struct_0(k9_yellow_6(A_201,B_202)))
      | ~ v3_pre_topc(C_200,A_201)
      | ~ r2_hidden(B_202,C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_1329,c_10])).

tff(c_38,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4093,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4083,c_38])).

tff(c_4099,plain,
    ( ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1368,c_4093])).

tff(c_4100,plain,
    ( ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4099])).

tff(c_4104,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4100])).

tff(c_4108,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_4104])).

tff(c_4207,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4204,c_4108])).

tff(c_4240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_4207])).

tff(c_4241,plain,(
    ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4100])).

tff(c_4245,plain,
    ( v1_xboole_0(k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_4241])).

tff(c_4248,plain,(
    v1_xboole_0(k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_4245])).

tff(c_4250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_831,c_4248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.95  
% 5.18/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.96  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.18/1.96  
% 5.18/1.96  %Foreground sorts:
% 5.18/1.96  
% 5.18/1.96  
% 5.18/1.96  %Background operators:
% 5.18/1.96  
% 5.18/1.96  
% 5.18/1.96  %Foreground operators:
% 5.18/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.18/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.18/1.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.18/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.18/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.18/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.18/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.18/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.96  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.18/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.18/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.18/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.18/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.96  
% 5.18/1.97  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.18/1.97  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.18/1.97  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 5.18/1.97  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.18/1.97  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.18/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.18/1.97  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.18/1.97  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.18/1.97  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.18/1.97  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.18/1.97  tff(f_78, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.18/1.97  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.18/1.97  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.18/1.97  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.18/1.97  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_729, plain, (![A_101, B_102, C_103]: ('#skF_1'(A_101, B_102, C_103)=C_103 | ~m1_subset_1(C_103, u1_struct_0(k9_yellow_6(A_101, B_102))) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.18/1.97  tff(c_735, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_729])).
% 5.18/1.97  tff(c_742, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_735])).
% 5.18/1.97  tff(c_743, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_742])).
% 5.18/1.97  tff(c_753, plain, (![B_104, A_105, C_106]: (r2_hidden(B_104, '#skF_1'(A_105, B_104, C_106)) | ~m1_subset_1(C_106, u1_struct_0(k9_yellow_6(A_105, B_104))) | ~m1_subset_1(B_104, u1_struct_0(A_105)) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.18/1.97  tff(c_757, plain, (r2_hidden('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_753])).
% 5.18/1.97  tff(c_764, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_743, c_757])).
% 5.18/1.97  tff(c_765, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_764])).
% 5.18/1.97  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.18/1.97  tff(c_206, plain, (![C_79, B_80, A_81]: (~v1_xboole_0(C_79) | ~m1_subset_1(B_80, k1_zfmisc_1(C_79)) | ~r2_hidden(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.18/1.97  tff(c_209, plain, (![B_15, A_81, A_14]: (~v1_xboole_0(B_15) | ~r2_hidden(A_81, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_16, c_206])).
% 5.18/1.97  tff(c_821, plain, (![B_112]: (~v1_xboole_0(B_112) | ~r1_tarski('#skF_4', B_112))), inference(resolution, [status(thm)], [c_765, c_209])).
% 5.18/1.97  tff(c_831, plain, (![B_6]: (~v1_xboole_0(k2_xboole_0('#skF_4', B_6)))), inference(resolution, [status(thm)], [c_6, c_821])).
% 5.18/1.97  tff(c_53, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/1.97  tff(c_68, plain, (![A_62, B_61]: (r1_tarski(A_62, k2_xboole_0(B_61, A_62)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_6])).
% 5.18/1.97  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_732, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_729])).
% 5.18/1.97  tff(c_738, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_732])).
% 5.18/1.97  tff(c_739, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_50, c_738])).
% 5.18/1.97  tff(c_755, plain, (r2_hidden('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_753])).
% 5.18/1.97  tff(c_760, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_739, c_755])).
% 5.18/1.97  tff(c_761, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_760])).
% 5.18/1.97  tff(c_498, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.18/1.97  tff(c_906, plain, (![A_119, B_120, A_121]: (m1_subset_1(A_119, B_120) | ~r2_hidden(A_119, A_121) | ~r1_tarski(A_121, B_120))), inference(resolution, [status(thm)], [c_16, c_498])).
% 5.18/1.97  tff(c_1049, plain, (![B_131]: (m1_subset_1('#skF_3', B_131) | ~r1_tarski('#skF_5', B_131))), inference(resolution, [status(thm)], [c_761, c_906])).
% 5.18/1.97  tff(c_1063, plain, (![B_61]: (m1_subset_1('#skF_3', k2_xboole_0(B_61, '#skF_5')))), inference(resolution, [status(thm)], [c_68, c_1049])).
% 5.18/1.97  tff(c_12, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.18/1.97  tff(c_927, plain, (![A_123, B_124, C_125]: (m1_subset_1('#skF_1'(A_123, B_124, C_125), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(C_125, u1_struct_0(k9_yellow_6(A_123, B_124))) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.18/1.97  tff(c_937, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_743, c_927])).
% 5.18/1.97  tff(c_945, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_937])).
% 5.18/1.97  tff(c_946, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_945])).
% 5.18/1.97  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.18/1.97  tff(c_959, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_946, c_14])).
% 5.18/1.97  tff(c_940, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_739, c_927])).
% 5.18/1.97  tff(c_948, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_940])).
% 5.18/1.97  tff(c_949, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_948])).
% 5.18/1.97  tff(c_982, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_949, c_14])).
% 5.18/1.97  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.18/1.97  tff(c_990, plain, (k2_xboole_0('#skF_5', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_982, c_4])).
% 5.18/1.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/1.97  tff(c_282, plain, (![A_87, C_88, B_89]: (r1_tarski(k2_xboole_0(A_87, C_88), k2_xboole_0(B_89, C_88)) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/1.97  tff(c_1380, plain, (![A_143, B_144, A_145]: (r1_tarski(k2_xboole_0(A_143, B_144), k2_xboole_0(B_144, A_145)) | ~r1_tarski(A_143, A_145))), inference(superposition, [status(thm), theory('equality')], [c_2, c_282])).
% 5.18/1.97  tff(c_4204, plain, (![A_210]: (r1_tarski(k2_xboole_0(A_210, '#skF_5'), u1_struct_0('#skF_2')) | ~r1_tarski(A_210, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_990, c_1380])).
% 5.18/1.97  tff(c_791, plain, (![A_108, B_109, C_110]: (v3_pre_topc('#skF_1'(A_108, B_109, C_110), A_108) | ~m1_subset_1(C_110, u1_struct_0(k9_yellow_6(A_108, B_109))) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.18/1.97  tff(c_793, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_791])).
% 5.18/1.97  tff(c_798, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_739, c_793])).
% 5.18/1.97  tff(c_799, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_798])).
% 5.18/1.97  tff(c_795, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_791])).
% 5.18/1.97  tff(c_802, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_743, c_795])).
% 5.18/1.97  tff(c_803, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_802])).
% 5.18/1.97  tff(c_1116, plain, (![B_134, C_135, A_136]: (v3_pre_topc(k2_xboole_0(B_134, C_135), A_136) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~v3_pre_topc(C_135, A_136) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_136))) | ~v3_pre_topc(B_134, A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.18/1.97  tff(c_1120, plain, (![B_134]: (v3_pre_topc(k2_xboole_0(B_134, '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_134, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_946, c_1116])).
% 5.18/1.97  tff(c_1351, plain, (![B_142]: (v3_pre_topc(k2_xboole_0(B_142, '#skF_4'), '#skF_2') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_142, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_803, c_1120])).
% 5.18/1.97  tff(c_1354, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_949, c_1351])).
% 5.18/1.97  tff(c_1368, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_2, c_1354])).
% 5.18/1.97  tff(c_1329, plain, (![C_139, A_140, B_141]: (r2_hidden(C_139, u1_struct_0(k9_yellow_6(A_140, B_141))) | ~v3_pre_topc(C_139, A_140) | ~r2_hidden(B_141, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.18/1.97  tff(c_10, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.18/1.97  tff(c_4083, plain, (![C_200, A_201, B_202]: (m1_subset_1(C_200, u1_struct_0(k9_yellow_6(A_201, B_202))) | ~v3_pre_topc(C_200, A_201) | ~r2_hidden(B_202, C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_1329, c_10])).
% 5.18/1.97  tff(c_38, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.18/1.97  tff(c_4093, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4083, c_38])).
% 5.18/1.97  tff(c_4099, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1368, c_4093])).
% 5.18/1.97  tff(c_4100, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_4099])).
% 5.18/1.97  tff(c_4104, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_4100])).
% 5.18/1.97  tff(c_4108, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_4104])).
% 5.18/1.97  tff(c_4207, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4204, c_4108])).
% 5.18/1.97  tff(c_4240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_959, c_4207])).
% 5.18/1.97  tff(c_4241, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_4100])).
% 5.18/1.97  tff(c_4245, plain, (v1_xboole_0(k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_4241])).
% 5.18/1.97  tff(c_4248, plain, (v1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_4245])).
% 5.18/1.97  tff(c_4250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_831, c_4248])).
% 5.18/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.97  
% 5.18/1.97  Inference rules
% 5.18/1.97  ----------------------
% 5.18/1.97  #Ref     : 0
% 5.18/1.97  #Sup     : 1064
% 5.18/1.97  #Fact    : 0
% 5.18/1.97  #Define  : 0
% 5.18/1.97  #Split   : 1
% 5.18/1.97  #Chain   : 0
% 5.18/1.97  #Close   : 0
% 5.18/1.97  
% 5.18/1.97  Ordering : KBO
% 5.18/1.97  
% 5.18/1.97  Simplification rules
% 5.18/1.97  ----------------------
% 5.18/1.97  #Subsume      : 239
% 5.18/1.97  #Demod        : 1027
% 5.18/1.97  #Tautology    : 491
% 5.18/1.97  #SimpNegUnit  : 33
% 5.18/1.97  #BackRed      : 0
% 5.18/1.97  
% 5.18/1.97  #Partial instantiations: 0
% 5.18/1.97  #Strategies tried      : 1
% 5.18/1.97  
% 5.18/1.97  Timing (in seconds)
% 5.18/1.97  ----------------------
% 5.18/1.98  Preprocessing        : 0.31
% 5.18/1.98  Parsing              : 0.17
% 5.18/1.98  CNF conversion       : 0.02
% 5.18/1.98  Main loop            : 0.90
% 5.18/1.98  Inferencing          : 0.24
% 5.18/1.98  Reduction            : 0.42
% 5.18/1.98  Demodulation         : 0.35
% 5.18/1.98  BG Simplification    : 0.03
% 5.18/1.98  Subsumption          : 0.16
% 5.18/1.98  Abstraction          : 0.04
% 5.18/1.98  MUC search           : 0.00
% 5.18/1.98  Cooper               : 0.00
% 5.18/1.98  Total                : 1.24
% 5.18/1.98  Index Insertion      : 0.00
% 5.18/1.98  Index Deletion       : 0.00
% 5.18/1.98  Index Matching       : 0.00
% 5.18/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
