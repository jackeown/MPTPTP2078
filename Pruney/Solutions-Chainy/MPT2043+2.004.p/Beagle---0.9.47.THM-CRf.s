%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:23 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 135 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 236 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_58,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_64,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))
     => ( v13_waybel_0(B,k3_yellow_1(A))
      <=> ! [C,D] :
            ( ( r1_tarski(C,D)
              & r1_tarski(D,A)
              & r2_hidden(C,B) )
           => r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [B_17] :
      ( ~ v1_subset_1(B_17,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_165,plain,(
    ! [B_45] :
      ( ~ v1_subset_1(B_45,B_45)
      | ~ r1_tarski(B_45,B_45) ) ),
    inference(resolution,[status(thm)],[c_158,c_32])).

tff(c_169,plain,(
    ! [B_45] : ~ v1_subset_1(B_45,B_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_165])).

tff(c_50,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_13] : k9_setfam_1(A_13) = k1_zfmisc_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [A_37] : k2_yellow_1(k1_zfmisc_1(A_37)) = k3_yellow_1(A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_24,plain,(
    ! [A_14] : u1_struct_0(k2_yellow_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [A_37] : u1_struct_0(k3_yellow_1(A_37)) = k1_zfmisc_1(A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_24])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_48])).

tff(c_238,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1('#skF_1'(A_58,B_59),A_58)
      | B_59 = A_58
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_252,plain,(
    ! [B_9,B_59] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_9),B_59),B_9)
      | k1_zfmisc_1(B_9) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(B_9))) ) ),
    inference(resolution,[status(thm)],[c_238,c_16])).

tff(c_44,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [A_7] : m1_subset_1('#skF_6',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_148,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_156,plain,(
    ! [A_7] : r1_tarski('#skF_6',A_7) ),
    inference(resolution,[status(thm)],[c_90,c_148])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ! [D_25,B_19,C_24,A_18] :
      ( r2_hidden(D_25,B_19)
      | ~ r2_hidden(C_24,B_19)
      | ~ r1_tarski(D_25,A_18)
      | ~ r1_tarski(C_24,D_25)
      | ~ v13_waybel_0(B_19,k3_yellow_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18)))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_487,plain,(
    ! [D_91,B_92,C_93,A_94] :
      ( r2_hidden(D_91,B_92)
      | ~ r2_hidden(C_93,B_92)
      | ~ r1_tarski(D_91,A_94)
      | ~ r1_tarski(C_93,D_91)
      | ~ v13_waybel_0(B_92,k3_yellow_1(A_94))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_34])).

tff(c_489,plain,(
    ! [D_91,A_94] :
      ( r2_hidden(D_91,'#skF_5')
      | ~ r1_tarski(D_91,A_94)
      | ~ r1_tarski('#skF_6',D_91)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_94))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(resolution,[status(thm)],[c_46,c_487])).

tff(c_572,plain,(
    ! [D_104,A_105] :
      ( r2_hidden(D_104,'#skF_5')
      | ~ r1_tarski(D_104,A_105)
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_105))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_489])).

tff(c_843,plain,(
    ! [B_128,B_129] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1(B_128),B_129),'#skF_5')
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(B_128))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(B_128)))
      | k1_zfmisc_1(B_128) = B_129
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(B_128))) ) ),
    inference(resolution,[status(thm)],[c_252,c_572])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | B_5 = A_4
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_870,plain,(
    ! [B_130] :
      ( ~ v13_waybel_0('#skF_5',k3_yellow_1(B_130))
      | k1_zfmisc_1(B_130) = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(B_130))) ) ),
    inference(resolution,[status(thm)],[c_843,c_10])).

tff(c_879,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1('#skF_4'))
    | k1_zfmisc_1('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_132,c_870])).

tff(c_884,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_879])).

tff(c_155,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_132,c_148])).

tff(c_171,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,
    ( k1_zfmisc_1('#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_zfmisc_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_155,c_171])).

tff(c_197,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_890,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_197])).

tff(c_897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_890])).

tff(c_898,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_54,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_122,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_54])).

tff(c_902,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_122])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.51  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.16/1.51  
% 3.16/1.51  %Foreground sorts:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Background operators:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Foreground operators:
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.16/1.51  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.16/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.51  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.16/1.51  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.16/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.51  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.16/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.51  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.51  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.16/1.51  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.16/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.51  
% 3.16/1.53  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.53  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.53  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.16/1.53  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.16/1.53  tff(f_58, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.16/1.53  tff(f_64, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 3.16/1.53  tff(f_62, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.16/1.53  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.16/1.53  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.16/1.53  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.16/1.53  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) => (v13_waybel_0(B, k3_yellow_1(A)) <=> (![C, D]: (((r1_tarski(C, D) & r1_tarski(D, A)) & r2_hidden(C, B)) => r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 3.16/1.53  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.53  tff(c_158, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.53  tff(c_32, plain, (![B_17]: (~v1_subset_1(B_17, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.53  tff(c_165, plain, (![B_45]: (~v1_subset_1(B_45, B_45) | ~r1_tarski(B_45, B_45))), inference(resolution, [status(thm)], [c_158, c_32])).
% 3.16/1.53  tff(c_169, plain, (![B_45]: (~v1_subset_1(B_45, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_165])).
% 3.16/1.53  tff(c_50, plain, (v13_waybel_0('#skF_5', k3_yellow_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_22, plain, (![A_13]: (k9_setfam_1(A_13)=k1_zfmisc_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.53  tff(c_28, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.53  tff(c_107, plain, (![A_37]: (k2_yellow_1(k1_zfmisc_1(A_37))=k3_yellow_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 3.16/1.53  tff(c_24, plain, (![A_14]: (u1_struct_0(k2_yellow_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.53  tff(c_116, plain, (![A_37]: (u1_struct_0(k3_yellow_1(A_37))=k1_zfmisc_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_107, c_24])).
% 3.16/1.53  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_132, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_48])).
% 3.16/1.53  tff(c_238, plain, (![A_58, B_59]: (m1_subset_1('#skF_1'(A_58, B_59), A_58) | B_59=A_58 | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.53  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.53  tff(c_252, plain, (![B_9, B_59]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_9), B_59), B_9) | k1_zfmisc_1(B_9)=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(B_9))))), inference(resolution, [status(thm)], [c_238, c_16])).
% 3.16/1.53  tff(c_44, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_62, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.53  tff(c_66, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_44, c_62])).
% 3.16/1.53  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.16/1.53  tff(c_90, plain, (![A_7]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 3.16/1.53  tff(c_148, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.53  tff(c_156, plain, (![A_7]: (r1_tarski('#skF_6', A_7))), inference(resolution, [status(thm)], [c_90, c_148])).
% 3.16/1.53  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_34, plain, (![D_25, B_19, C_24, A_18]: (r2_hidden(D_25, B_19) | ~r2_hidden(C_24, B_19) | ~r1_tarski(D_25, A_18) | ~r1_tarski(C_24, D_25) | ~v13_waybel_0(B_19, k3_yellow_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_18)))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.53  tff(c_487, plain, (![D_91, B_92, C_93, A_94]: (r2_hidden(D_91, B_92) | ~r2_hidden(C_93, B_92) | ~r1_tarski(D_91, A_94) | ~r1_tarski(C_93, D_91) | ~v13_waybel_0(B_92, k3_yellow_1(A_94)) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_34])).
% 3.16/1.53  tff(c_489, plain, (![D_91, A_94]: (r2_hidden(D_91, '#skF_5') | ~r1_tarski(D_91, A_94) | ~r1_tarski('#skF_6', D_91) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_94)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(resolution, [status(thm)], [c_46, c_487])).
% 3.16/1.53  tff(c_572, plain, (![D_104, A_105]: (r2_hidden(D_104, '#skF_5') | ~r1_tarski(D_104, A_105) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_105)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_489])).
% 3.16/1.53  tff(c_843, plain, (![B_128, B_129]: (r2_hidden('#skF_1'(k1_zfmisc_1(B_128), B_129), '#skF_5') | ~v13_waybel_0('#skF_5', k3_yellow_1(B_128)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(B_128))) | k1_zfmisc_1(B_128)=B_129 | ~m1_subset_1(B_129, k1_zfmisc_1(k1_zfmisc_1(B_128))))), inference(resolution, [status(thm)], [c_252, c_572])).
% 3.16/1.53  tff(c_10, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | B_5=A_4 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.53  tff(c_870, plain, (![B_130]: (~v13_waybel_0('#skF_5', k3_yellow_1(B_130)) | k1_zfmisc_1(B_130)='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(B_130))))), inference(resolution, [status(thm)], [c_843, c_10])).
% 3.16/1.53  tff(c_879, plain, (~v13_waybel_0('#skF_5', k3_yellow_1('#skF_4')) | k1_zfmisc_1('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_132, c_870])).
% 3.16/1.53  tff(c_884, plain, (k1_zfmisc_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_879])).
% 3.16/1.53  tff(c_155, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_132, c_148])).
% 3.16/1.53  tff(c_171, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.53  tff(c_178, plain, (k1_zfmisc_1('#skF_4')='#skF_5' | ~r1_tarski(k1_zfmisc_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_155, c_171])).
% 3.16/1.53  tff(c_197, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_178])).
% 3.16/1.53  tff(c_890, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_884, c_197])).
% 3.16/1.53  tff(c_897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_890])).
% 3.16/1.53  tff(c_898, plain, (k1_zfmisc_1('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_178])).
% 3.16/1.53  tff(c_54, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.16/1.53  tff(c_122, plain, (v1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_54])).
% 3.16/1.53  tff(c_902, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_122])).
% 3.16/1.53  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_902])).
% 3.16/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  Inference rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Ref     : 0
% 3.16/1.53  #Sup     : 176
% 3.16/1.53  #Fact    : 0
% 3.16/1.53  #Define  : 0
% 3.16/1.53  #Split   : 7
% 3.16/1.53  #Chain   : 0
% 3.16/1.53  #Close   : 0
% 3.16/1.53  
% 3.16/1.53  Ordering : KBO
% 3.16/1.53  
% 3.16/1.53  Simplification rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Subsume      : 33
% 3.16/1.53  #Demod        : 128
% 3.16/1.53  #Tautology    : 57
% 3.16/1.53  #SimpNegUnit  : 3
% 3.16/1.53  #BackRed      : 15
% 3.16/1.53  
% 3.16/1.53  #Partial instantiations: 0
% 3.16/1.53  #Strategies tried      : 1
% 3.16/1.53  
% 3.16/1.53  Timing (in seconds)
% 3.16/1.53  ----------------------
% 3.16/1.53  Preprocessing        : 0.35
% 3.16/1.53  Parsing              : 0.18
% 3.16/1.53  CNF conversion       : 0.03
% 3.16/1.53  Main loop            : 0.40
% 3.16/1.53  Inferencing          : 0.15
% 3.16/1.53  Reduction            : 0.13
% 3.16/1.53  Demodulation         : 0.09
% 3.16/1.53  BG Simplification    : 0.02
% 3.16/1.53  Subsumption          : 0.08
% 3.16/1.53  Abstraction          : 0.02
% 3.16/1.53  MUC search           : 0.00
% 3.16/1.53  Cooper               : 0.00
% 3.16/1.53  Total                : 0.78
% 3.16/1.53  Index Insertion      : 0.00
% 3.16/1.53  Index Deletion       : 0.00
% 3.16/1.53  Index Matching       : 0.00
% 3.16/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
