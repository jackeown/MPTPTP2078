%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:16 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 502 expanded)
%              Number of leaves         :   30 ( 207 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (1979 expanded)
%              Number of equality atoms :   12 (  91 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_130,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(c_50,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_150,plain,(
    ! [A_105,B_106,C_107] :
      ( '#skF_2'(A_105,B_106,C_107) = C_107
      | ~ m1_subset_1(C_107,u1_struct_0(k9_yellow_6(A_105,B_106)))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_161,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_5') = '#skF_5'
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_169,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_161])).

tff(c_170,plain,(
    '#skF_2'('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_169])).

tff(c_239,plain,(
    ! [B_130,A_131,C_132] :
      ( r2_hidden(B_130,'#skF_2'(A_131,B_130,C_132))
      | ~ m1_subset_1(C_132,u1_struct_0(k9_yellow_6(A_131,B_130)))
      | ~ m1_subset_1(B_130,u1_struct_0(A_131))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_247,plain,
    ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_254,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_170,c_247])).

tff(c_255,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_254])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_4',B_133)
      | ~ r1_tarski('#skF_5',B_133) ) ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_377,plain,(
    ! [B_146,B_147] :
      ( r2_hidden('#skF_4',B_146)
      | ~ r1_tarski(B_147,B_146)
      | ~ r1_tarski('#skF_5',B_147) ) ),
    inference(resolution,[status(thm)],[c_274,c_2])).

tff(c_389,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_4',k2_xboole_0(A_6,B_7))
      | ~ r1_tarski('#skF_5',A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_377])).

tff(c_544,plain,(
    ! [A_187,B_188,C_189] :
      ( m1_subset_1('#skF_2'(A_187,B_188,C_189),k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(C_189,u1_struct_0(k9_yellow_6(A_187,B_188)))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_554,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_544])).

tff(c_561,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_554])).

tff(c_562,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_561])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_164,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_173,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_164])).

tff(c_174,plain,(
    '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_173])).

tff(c_551,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_3','#skF_4')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_544])).

tff(c_558,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_36,c_551])).

tff(c_559,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_558])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( k4_subset_1(A_11,B_12,C_13) = k2_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1155,plain,(
    ! [B_241] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_241,'#skF_6') = k2_xboole_0(B_241,'#skF_6')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_559,c_12])).

tff(c_1194,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_562,c_1155])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k4_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1209,plain,
    ( m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_10])).

tff(c_1215,plain,(
    m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_559,c_1209])).

tff(c_808,plain,(
    ! [C_219,A_220,B_221] :
      ( r2_hidden(C_219,u1_struct_0(k9_yellow_6(A_220,B_221)))
      | ~ v3_pre_topc(C_219,A_220)
      | ~ r2_hidden(B_221,C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_subset_1(B_221,u1_struct_0(A_220))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1764,plain,(
    ! [C_268,A_269,B_270] :
      ( m1_subset_1(C_268,u1_struct_0(k9_yellow_6(A_269,B_270)))
      | ~ v3_pre_topc(C_268,A_269)
      | ~ r2_hidden(B_270,C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_808,c_14])).

tff(c_34,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1782,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1764,c_34])).

tff(c_1796,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1215,c_1782])).

tff(c_1797,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1796])).

tff(c_1798,plain,(
    ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1797])).

tff(c_1804,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_389,c_1798])).

tff(c_1815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1804])).

tff(c_1816,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1797])).

tff(c_196,plain,(
    ! [A_113,B_114,C_115] :
      ( v3_pre_topc('#skF_2'(A_113,B_114,C_115),A_113)
      | ~ m1_subset_1(C_115,u1_struct_0(k9_yellow_6(A_113,B_114)))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_204,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_196])).

tff(c_211,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_170,c_204])).

tff(c_212,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_211])).

tff(c_206,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_196])).

tff(c_215,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_174,c_206])).

tff(c_216,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_215])).

tff(c_26,plain,(
    ! [A_22,B_30,C_34] :
      ( m1_subset_1('#skF_2'(A_22,B_30,C_34),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(C_34,u1_struct_0(k9_yellow_6(A_22,B_30)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_643,plain,(
    ! [B_207,C_208,A_209] :
      ( v3_pre_topc(k2_xboole_0(B_207,C_208),A_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ v3_pre_topc(C_208,A_209)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ v3_pre_topc(B_207,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3004,plain,(
    ! [B_320,A_321,B_322,C_323] :
      ( v3_pre_topc(k2_xboole_0(B_320,'#skF_2'(A_321,B_322,C_323)),A_321)
      | ~ v3_pre_topc('#skF_2'(A_321,B_322,C_323),A_321)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ v3_pre_topc(B_320,A_321)
      | ~ m1_subset_1(C_323,u1_struct_0(k9_yellow_6(A_321,B_322)))
      | ~ m1_subset_1(B_322,u1_struct_0(A_321))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_26,c_643])).

tff(c_3007,plain,(
    ! [B_320] :
      ( v3_pre_topc(k2_xboole_0(B_320,'#skF_6'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_320,'#skF_3')
      | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_3','#skF_4')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_3004])).

tff(c_3012,plain,(
    ! [B_320] :
      ( v3_pre_topc(k2_xboole_0(B_320,'#skF_6'),'#skF_3')
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_320,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_36,c_216,c_174,c_3007])).

tff(c_3040,plain,(
    ! [B_328] :
      ( v3_pre_topc(k2_xboole_0(B_328,'#skF_6'),'#skF_3')
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_328,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3012])).

tff(c_3091,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_562,c_3040])).

tff(c_3129,plain,(
    v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_3091])).

tff(c_3131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1816,c_3129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  
% 5.35/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.03  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.35/2.03  
% 5.35/2.03  %Foreground sorts:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Background operators:
% 5.35/2.03  
% 5.35/2.03  
% 5.35/2.03  %Foreground operators:
% 5.35/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.35/2.03  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.35/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.35/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.35/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.03  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.35/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.35/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.03  
% 5.35/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.05  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.35/2.05  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.35/2.05  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 5.35/2.05  tff(f_46, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.35/2.05  tff(f_40, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.35/2.05  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.35/2.05  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.35/2.05  tff(f_70, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.35/2.05  tff(c_50, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_58, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_50, c_4])).
% 5.35/2.05  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.35/2.05  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_150, plain, (![A_105, B_106, C_107]: ('#skF_2'(A_105, B_106, C_107)=C_107 | ~m1_subset_1(C_107, u1_struct_0(k9_yellow_6(A_105, B_106))) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/2.05  tff(c_161, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_150])).
% 5.35/2.05  tff(c_169, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_161])).
% 5.35/2.05  tff(c_170, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_169])).
% 5.35/2.05  tff(c_239, plain, (![B_130, A_131, C_132]: (r2_hidden(B_130, '#skF_2'(A_131, B_130, C_132)) | ~m1_subset_1(C_132, u1_struct_0(k9_yellow_6(A_131, B_130))) | ~m1_subset_1(B_130, u1_struct_0(A_131)) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/2.05  tff(c_247, plain, (r2_hidden('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_239])).
% 5.35/2.05  tff(c_254, plain, (r2_hidden('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_170, c_247])).
% 5.35/2.05  tff(c_255, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_254])).
% 5.35/2.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_274, plain, (![B_133]: (r2_hidden('#skF_4', B_133) | ~r1_tarski('#skF_5', B_133))), inference(resolution, [status(thm)], [c_255, c_2])).
% 5.35/2.05  tff(c_377, plain, (![B_146, B_147]: (r2_hidden('#skF_4', B_146) | ~r1_tarski(B_147, B_146) | ~r1_tarski('#skF_5', B_147))), inference(resolution, [status(thm)], [c_274, c_2])).
% 5.35/2.05  tff(c_389, plain, (![A_6, B_7]: (r2_hidden('#skF_4', k2_xboole_0(A_6, B_7)) | ~r1_tarski('#skF_5', A_6))), inference(resolution, [status(thm)], [c_8, c_377])).
% 5.35/2.05  tff(c_544, plain, (![A_187, B_188, C_189]: (m1_subset_1('#skF_2'(A_187, B_188, C_189), k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(C_189, u1_struct_0(k9_yellow_6(A_187, B_188))) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/2.05  tff(c_554, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170, c_544])).
% 5.35/2.05  tff(c_561, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_554])).
% 5.35/2.05  tff(c_562, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_561])).
% 5.35/2.05  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_164, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_150])).
% 5.35/2.05  tff(c_173, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_164])).
% 5.35/2.05  tff(c_174, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_173])).
% 5.35/2.05  tff(c_551, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_174, c_544])).
% 5.35/2.05  tff(c_558, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_36, c_551])).
% 5.35/2.05  tff(c_559, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_558])).
% 5.35/2.05  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_subset_1(A_11, B_12, C_13)=k2_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.35/2.05  tff(c_1155, plain, (![B_241]: (k4_subset_1(u1_struct_0('#skF_3'), B_241, '#skF_6')=k2_xboole_0(B_241, '#skF_6') | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_559, c_12])).
% 5.35/2.05  tff(c_1194, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6')=k2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_562, c_1155])).
% 5.35/2.05  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k4_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.35/2.05  tff(c_1209, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_10])).
% 5.35/2.05  tff(c_1215, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_559, c_1209])).
% 5.35/2.05  tff(c_808, plain, (![C_219, A_220, B_221]: (r2_hidden(C_219, u1_struct_0(k9_yellow_6(A_220, B_221))) | ~v3_pre_topc(C_219, A_220) | ~r2_hidden(B_221, C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_subset_1(B_221, u1_struct_0(A_220)) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.35/2.05  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/2.05  tff(c_1764, plain, (![C_268, A_269, B_270]: (m1_subset_1(C_268, u1_struct_0(k9_yellow_6(A_269, B_270))) | ~v3_pre_topc(C_268, A_269) | ~r2_hidden(B_270, C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(u1_struct_0(A_269))) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_808, c_14])).
% 5.35/2.05  tff(c_34, plain, (~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.35/2.05  tff(c_1782, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1764, c_34])).
% 5.35/2.05  tff(c_1796, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1215, c_1782])).
% 5.35/2.05  tff(c_1797, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1796])).
% 5.35/2.05  tff(c_1798, plain, (~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1797])).
% 5.35/2.05  tff(c_1804, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_389, c_1798])).
% 5.35/2.05  tff(c_1815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1804])).
% 5.35/2.05  tff(c_1816, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3')), inference(splitRight, [status(thm)], [c_1797])).
% 5.35/2.05  tff(c_196, plain, (![A_113, B_114, C_115]: (v3_pre_topc('#skF_2'(A_113, B_114, C_115), A_113) | ~m1_subset_1(C_115, u1_struct_0(k9_yellow_6(A_113, B_114))) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/2.05  tff(c_204, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_196])).
% 5.35/2.05  tff(c_211, plain, (v3_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_170, c_204])).
% 5.35/2.05  tff(c_212, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_211])).
% 5.35/2.05  tff(c_206, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_196])).
% 5.35/2.05  tff(c_215, plain, (v3_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_174, c_206])).
% 5.35/2.05  tff(c_216, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_215])).
% 5.35/2.05  tff(c_26, plain, (![A_22, B_30, C_34]: (m1_subset_1('#skF_2'(A_22, B_30, C_34), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(C_34, u1_struct_0(k9_yellow_6(A_22, B_30))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/2.05  tff(c_643, plain, (![B_207, C_208, A_209]: (v3_pre_topc(k2_xboole_0(B_207, C_208), A_209) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~v3_pre_topc(C_208, A_209) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_209))) | ~v3_pre_topc(B_207, A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.35/2.05  tff(c_3004, plain, (![B_320, A_321, B_322, C_323]: (v3_pre_topc(k2_xboole_0(B_320, '#skF_2'(A_321, B_322, C_323)), A_321) | ~v3_pre_topc('#skF_2'(A_321, B_322, C_323), A_321) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~v3_pre_topc(B_320, A_321) | ~m1_subset_1(C_323, u1_struct_0(k9_yellow_6(A_321, B_322))) | ~m1_subset_1(B_322, u1_struct_0(A_321)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_26, c_643])).
% 5.35/2.05  tff(c_3007, plain, (![B_320]: (v3_pre_topc(k2_xboole_0(B_320, '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_320, '#skF_3') | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_3004])).
% 5.35/2.05  tff(c_3012, plain, (![B_320]: (v3_pre_topc(k2_xboole_0(B_320, '#skF_6'), '#skF_3') | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_320, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_36, c_216, c_174, c_3007])).
% 5.35/2.05  tff(c_3040, plain, (![B_328]: (v3_pre_topc(k2_xboole_0(B_328, '#skF_6'), '#skF_3') | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_328, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_3012])).
% 5.35/2.05  tff(c_3091, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_562, c_3040])).
% 5.35/2.05  tff(c_3129, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_3091])).
% 5.35/2.05  tff(c_3131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1816, c_3129])).
% 5.35/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.05  
% 5.35/2.05  Inference rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Ref     : 0
% 5.35/2.05  #Sup     : 659
% 5.35/2.05  #Fact    : 0
% 5.35/2.05  #Define  : 0
% 5.35/2.05  #Split   : 1
% 5.35/2.05  #Chain   : 0
% 5.35/2.05  #Close   : 0
% 5.35/2.05  
% 5.35/2.05  Ordering : KBO
% 5.35/2.05  
% 5.35/2.05  Simplification rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Subsume      : 47
% 5.35/2.05  #Demod        : 452
% 5.35/2.05  #Tautology    : 153
% 5.35/2.05  #SimpNegUnit  : 39
% 5.35/2.05  #BackRed      : 0
% 5.35/2.05  
% 5.35/2.05  #Partial instantiations: 0
% 5.35/2.05  #Strategies tried      : 1
% 5.35/2.05  
% 5.35/2.05  Timing (in seconds)
% 5.35/2.05  ----------------------
% 5.35/2.05  Preprocessing        : 0.36
% 5.35/2.05  Parsing              : 0.20
% 5.35/2.05  CNF conversion       : 0.03
% 5.35/2.05  Main loop            : 0.90
% 5.35/2.05  Inferencing          : 0.30
% 5.35/2.05  Reduction            : 0.30
% 5.35/2.05  Demodulation         : 0.22
% 5.35/2.05  BG Simplification    : 0.04
% 5.35/2.05  Subsumption          : 0.19
% 5.35/2.05  Abstraction          : 0.05
% 5.35/2.05  MUC search           : 0.00
% 5.35/2.05  Cooper               : 0.00
% 5.35/2.05  Total                : 1.30
% 5.35/2.05  Index Insertion      : 0.00
% 5.35/2.05  Index Deletion       : 0.00
% 5.35/2.05  Index Matching       : 0.00
% 5.35/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
