%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 368 expanded)
%              Number of leaves         :   41 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 (1047 expanded)
%              Number of equality atoms :   15 ( 142 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( m1_connsp_2(D,A,C)
                            & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_104,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_113,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_24,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_119,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_24])).

tff(c_122,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_119])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_139])).

tff(c_144,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_115,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_48])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_17] :
      ( v3_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_60,plain,(
    ! [D_57] :
      ( v4_pre_topc(D_57,'#skF_3')
      | ~ r2_hidden(D_57,'#skF_5')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_465,plain,(
    ! [D_107] :
      ( v4_pre_topc(D_107,'#skF_3')
      | ~ r2_hidden(D_107,'#skF_5')
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_60])).

tff(c_475,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_465])).

tff(c_495,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_56,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,'#skF_5')
      | ~ r2_hidden('#skF_4',D_57)
      | ~ v4_pre_topc(D_57,'#skF_3')
      | ~ v3_pre_topc(D_57,'#skF_3')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_502,plain,(
    ! [D_109] :
      ( r2_hidden(D_109,'#skF_5')
      | ~ r2_hidden('#skF_4',D_109)
      | ~ v4_pre_topc(D_109,'#skF_3')
      | ~ v3_pre_topc(D_109,'#skF_3')
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_56])).

tff(c_510,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_502])).

tff(c_516,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_510])).

tff(c_662,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_677,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_662])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_677])).

tff(c_682,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_684,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_687,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_684])).

tff(c_690,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_687])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_690])).

tff(c_693,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_58,plain,(
    ! [D_57] :
      ( r2_hidden('#skF_4',D_57)
      | ~ r2_hidden(D_57,'#skF_5')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_180,plain,(
    ! [D_83] :
      ( r2_hidden('#skF_4',D_83)
      | ~ r2_hidden(D_83,'#skF_5')
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_58])).

tff(c_189,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_180])).

tff(c_476,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_506,plain,
    ( r2_hidden('#skF_5','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_502])).

tff(c_513,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_506])).

tff(c_517,plain,(
    ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_614,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119),B_119)
      | v3_pre_topc(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_616,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_2'('#skF_3',B_119),B_119)
      | v3_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_614])).

tff(c_624,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_2'('#skF_3',B_119),B_119)
      | v3_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_616])).

tff(c_628,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_2'('#skF_3',B_120),B_120)
      | v3_pre_topc(B_120,'#skF_3')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_624])).

tff(c_631,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_5'),'#skF_5')
    | v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_628])).

tff(c_637,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_631])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_647,plain,(
    ~ r1_tarski('#skF_5','#skF_2'('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_637,c_18])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_647])).

tff(c_655,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_10,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_68,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_5') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66])).

tff(c_704,plain,(
    ! [A_123,B_124] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_123),B_124),A_123)
      | ~ v3_pre_topc(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_711,plain,(
    ! [A_123] :
      ( v4_pre_topc(u1_struct_0(A_123),A_123)
      | ~ v3_pre_topc('#skF_5',A_123)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_704])).

tff(c_716,plain,(
    ! [A_125] :
      ( v4_pre_topc(u1_struct_0(A_125),A_125)
      | ~ v3_pre_topc('#skF_5',A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_711])).

tff(c_719,plain,
    ( v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_716])).

tff(c_721,plain,(
    v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_655,c_719])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_693,c_721])).

tff(c_725,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_745,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_725,c_18])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.41  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.91/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.91/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.91/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.91/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.91/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.91/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.91/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.41  
% 2.91/1.43  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.91/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.43  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.91/1.43  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.91/1.43  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.91/1.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.91/1.43  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.91/1.43  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.91/1.43  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.91/1.43  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.43  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 2.91/1.43  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.91/1.43  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.91/1.43  tff(f_35, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.91/1.43  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 2.91/1.43  tff(c_44, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.43  tff(c_69, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2])).
% 2.91/1.43  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.43  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_104, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.43  tff(c_109, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_22, c_104])).
% 2.91/1.43  tff(c_113, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_109])).
% 2.91/1.43  tff(c_24, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.91/1.43  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113, c_24])).
% 2.91/1.43  tff(c_122, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_119])).
% 2.91/1.43  tff(c_124, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_122])).
% 2.91/1.43  tff(c_139, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_124])).
% 2.91/1.43  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_139])).
% 2.91/1.43  tff(c_144, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_122])).
% 2.91/1.43  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_115, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_48])).
% 2.91/1.43  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.43  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_26, plain, (![A_17]: (v3_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.91/1.43  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.43  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.43  tff(c_65, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.91/1.43  tff(c_60, plain, (![D_57]: (v4_pre_topc(D_57, '#skF_3') | ~r2_hidden(D_57, '#skF_5') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_465, plain, (![D_107]: (v4_pre_topc(D_107, '#skF_3') | ~r2_hidden(D_107, '#skF_5') | ~m1_subset_1(D_107, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_60])).
% 2.91/1.43  tff(c_475, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_65, c_465])).
% 2.91/1.43  tff(c_495, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_475])).
% 2.91/1.43  tff(c_56, plain, (![D_57]: (r2_hidden(D_57, '#skF_5') | ~r2_hidden('#skF_4', D_57) | ~v4_pre_topc(D_57, '#skF_3') | ~v3_pre_topc(D_57, '#skF_3') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_502, plain, (![D_109]: (r2_hidden(D_109, '#skF_5') | ~r2_hidden('#skF_4', D_109) | ~v4_pre_topc(D_109, '#skF_3') | ~v3_pre_topc(D_109, '#skF_3') | ~m1_subset_1(D_109, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_56])).
% 2.91/1.43  tff(c_510, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_65, c_502])).
% 2.91/1.43  tff(c_516, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_495, c_510])).
% 2.91/1.43  tff(c_662, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_516])).
% 2.91/1.43  tff(c_677, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_662])).
% 2.91/1.43  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_677])).
% 2.91/1.43  tff(c_682, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_516])).
% 2.91/1.43  tff(c_684, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_682])).
% 2.91/1.43  tff(c_687, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_684])).
% 2.91/1.43  tff(c_690, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_687])).
% 2.91/1.43  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_690])).
% 2.91/1.43  tff(c_693, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_682])).
% 2.91/1.43  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.43  tff(c_63, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 2.91/1.43  tff(c_58, plain, (![D_57]: (r2_hidden('#skF_4', D_57) | ~r2_hidden(D_57, '#skF_5') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.91/1.43  tff(c_180, plain, (![D_83]: (r2_hidden('#skF_4', D_83) | ~r2_hidden(D_83, '#skF_5') | ~m1_subset_1(D_83, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_58])).
% 2.91/1.43  tff(c_189, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_63, c_180])).
% 2.91/1.43  tff(c_476, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_189])).
% 2.91/1.43  tff(c_506, plain, (r2_hidden('#skF_5', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_502])).
% 2.91/1.43  tff(c_513, plain, (~r2_hidden('#skF_4', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_476, c_506])).
% 2.91/1.43  tff(c_517, plain, (~v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_513])).
% 2.91/1.43  tff(c_614, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119), B_119) | v3_pre_topc(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.91/1.43  tff(c_616, plain, (![B_119]: (r2_hidden('#skF_2'('#skF_3', B_119), B_119) | v3_pre_topc(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_614])).
% 2.91/1.43  tff(c_624, plain, (![B_119]: (r2_hidden('#skF_2'('#skF_3', B_119), B_119) | v3_pre_topc(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_616])).
% 2.91/1.43  tff(c_628, plain, (![B_120]: (r2_hidden('#skF_2'('#skF_3', B_120), B_120) | v3_pre_topc(B_120, '#skF_3') | ~m1_subset_1(B_120, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_624])).
% 2.91/1.43  tff(c_631, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5'), '#skF_5') | v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_628])).
% 2.91/1.43  tff(c_637, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_517, c_631])).
% 2.91/1.43  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.91/1.43  tff(c_647, plain, (~r1_tarski('#skF_5', '#skF_2'('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_637, c_18])).
% 2.91/1.43  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_647])).
% 2.91/1.43  tff(c_655, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_513])).
% 2.91/1.43  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.43  tff(c_67, plain, (![A_2]: (k1_subset_1(A_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 2.91/1.43  tff(c_10, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.43  tff(c_66, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.91/1.43  tff(c_68, plain, (![A_5]: (k3_subset_1(A_5, '#skF_5')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66])).
% 2.91/1.43  tff(c_704, plain, (![A_123, B_124]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_123), B_124), A_123) | ~v3_pre_topc(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.91/1.43  tff(c_711, plain, (![A_123]: (v4_pre_topc(u1_struct_0(A_123), A_123) | ~v3_pre_topc('#skF_5', A_123) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_68, c_704])).
% 2.91/1.43  tff(c_716, plain, (![A_125]: (v4_pre_topc(u1_struct_0(A_125), A_125) | ~v3_pre_topc('#skF_5', A_125) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_711])).
% 2.91/1.43  tff(c_719, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113, c_716])).
% 2.91/1.43  tff(c_721, plain, (v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_655, c_719])).
% 2.91/1.43  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_693, c_721])).
% 2.91/1.43  tff(c_725, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_475])).
% 2.91/1.43  tff(c_745, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_725, c_18])).
% 2.91/1.43  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_745])).
% 2.91/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  Inference rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Ref     : 0
% 2.91/1.43  #Sup     : 118
% 2.91/1.43  #Fact    : 0
% 2.91/1.43  #Define  : 0
% 2.91/1.43  #Split   : 15
% 2.91/1.43  #Chain   : 0
% 2.91/1.43  #Close   : 0
% 2.91/1.43  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 19
% 2.91/1.43  #Demod        : 89
% 2.91/1.43  #Tautology    : 33
% 2.91/1.43  #SimpNegUnit  : 24
% 2.91/1.43  #BackRed      : 1
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.43  Preprocessing        : 0.33
% 2.91/1.43  Parsing              : 0.17
% 2.91/1.43  CNF conversion       : 0.03
% 2.91/1.43  Main loop            : 0.33
% 2.91/1.43  Inferencing          : 0.11
% 2.91/1.43  Reduction            : 0.11
% 2.91/1.43  Demodulation         : 0.07
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.06
% 2.91/1.43  Abstraction          : 0.01
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.71
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
