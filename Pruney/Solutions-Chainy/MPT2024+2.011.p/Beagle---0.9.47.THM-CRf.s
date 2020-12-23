%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 26.22s
% Output     : CNFRefutation 26.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 577 expanded)
%              Number of leaves         :   39 ( 235 expanded)
%              Depth                    :   16
%              Number of atoms          :  315 (2201 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
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

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_146,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_474,plain,(
    ! [C_158,A_159,B_160] :
      ( m1_connsp_2(C_158,A_159,B_160)
      | ~ m1_subset_1(C_158,u1_struct_0(k9_yellow_6(A_159,B_160)))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_484,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_474])).

tff(c_492,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_484])).

tff(c_493,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_492])).

tff(c_46,plain,(
    ! [C_33,A_30,B_31] :
      ( m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_connsp_2(C_33,A_30,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_501,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_493,c_46])).

tff(c_504,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_501])).

tff(c_505,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_504])).

tff(c_539,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,B_162)
      | ~ m1_connsp_2(B_162,A_163,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_163))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_541,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_493,c_539])).

tff(c_546,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_505,c_64,c_541])).

tff(c_547,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_546])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_481,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_474])).

tff(c_488,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_481])).

tff(c_489,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_488])).

tff(c_495,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_489,c_46])).

tff(c_498,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_495])).

tff(c_499,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_498])).

tff(c_36,plain,(
    ! [A_16,B_17,C_18] :
      ( k4_subset_1(A_16,B_17,C_18) = k2_xboole_0(B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1466,plain,(
    ! [B_181] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_181,'#skF_6') = k2_xboole_0(B_181,'#skF_6')
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_505,c_36])).

tff(c_1518,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_499,c_1466])).

tff(c_34,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k4_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1560,plain,
    ( m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_34])).

tff(c_1564,plain,(
    m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_505,c_1560])).

tff(c_83,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_60,c_83])).

tff(c_120,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_2254,plain,(
    ! [B_196,C_197,A_198] :
      ( v3_pre_topc(k2_xboole_0(B_196,C_197),A_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ v3_pre_topc(C_197,A_198)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ v3_pre_topc(B_196,A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2284,plain,(
    ! [B_196] :
      ( v3_pre_topc(k2_xboole_0(B_196,'#skF_5'),'#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_196,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_499,c_2254])).

tff(c_2344,plain,(
    ! [B_196] :
      ( v3_pre_topc(k2_xboole_0(B_196,'#skF_5'),'#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_196,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2284])).

tff(c_45766,plain,(
    ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2344])).

tff(c_24,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1641,plain,(
    ! [C_183,A_184,B_185] :
      ( v3_pre_topc(C_183,A_184)
      | ~ r2_hidden(C_183,u1_struct_0(k9_yellow_6(A_184,B_185)))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_66722,plain,(
    ! [B_1468,A_1469,B_1470] :
      ( v3_pre_topc(B_1468,A_1469)
      | ~ m1_subset_1(B_1468,k1_zfmisc_1(u1_struct_0(A_1469)))
      | ~ m1_subset_1(B_1470,u1_struct_0(A_1469))
      | ~ l1_pre_topc(A_1469)
      | ~ v2_pre_topc(A_1469)
      | v2_struct_0(A_1469)
      | ~ m1_subset_1(B_1468,u1_struct_0(k9_yellow_6(A_1469,B_1470)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1469,B_1470))) ) ),
    inference(resolution,[status(thm)],[c_24,c_1641])).

tff(c_66796,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_62,c_66722])).

tff(c_66820,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_499,c_66796])).

tff(c_66822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_70,c_45766,c_66820])).

tff(c_66824,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2344])).

tff(c_2282,plain,(
    ! [B_196] :
      ( v3_pre_topc(k2_xboole_0(B_196,'#skF_6'),'#skF_3')
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_196,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_505,c_2254])).

tff(c_2341,plain,(
    ! [B_196] :
      ( v3_pre_topc(k2_xboole_0(B_196,'#skF_6'),'#skF_3')
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_196,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2282])).

tff(c_4002,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2341])).

tff(c_45569,plain,(
    ! [B_1051,A_1052,B_1053] :
      ( v3_pre_topc(B_1051,A_1052)
      | ~ m1_subset_1(B_1051,k1_zfmisc_1(u1_struct_0(A_1052)))
      | ~ m1_subset_1(B_1053,u1_struct_0(A_1052))
      | ~ l1_pre_topc(A_1052)
      | ~ v2_pre_topc(A_1052)
      | v2_struct_0(A_1052)
      | ~ m1_subset_1(B_1051,u1_struct_0(k9_yellow_6(A_1052,B_1053)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1052,B_1053))) ) ),
    inference(resolution,[status(thm)],[c_24,c_1641])).

tff(c_45646,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_60,c_45569])).

tff(c_45671,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_505,c_45646])).

tff(c_45673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_70,c_4002,c_45671])).

tff(c_66825,plain,(
    ! [B_1471] :
      ( v3_pre_topc(k2_xboole_0(B_1471,'#skF_6'),'#skF_3')
      | ~ m1_subset_1(B_1471,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_1471,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_66906,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_499,c_66825])).

tff(c_66957,plain,(
    v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66824,c_66906])).

tff(c_2926,plain,(
    ! [C_212,A_213,B_214] :
      ( r2_hidden(C_212,u1_struct_0(k9_yellow_6(A_213,B_214)))
      | ~ v3_pre_topc(C_212,A_213)
      | ~ r2_hidden(B_214,C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(B_214,u1_struct_0(A_213))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87029,plain,(
    ! [C_1897,A_1898,B_1899] :
      ( m1_subset_1(C_1897,u1_struct_0(k9_yellow_6(A_1898,B_1899)))
      | ~ v3_pre_topc(C_1897,A_1898)
      | ~ r2_hidden(B_1899,C_1897)
      | ~ m1_subset_1(C_1897,k1_zfmisc_1(u1_struct_0(A_1898)))
      | ~ m1_subset_1(B_1899,u1_struct_0(A_1898))
      | ~ l1_pre_topc(A_1898)
      | ~ v2_pre_topc(A_1898)
      | v2_struct_0(A_1898) ) ),
    inference(resolution,[status(thm)],[c_2926,c_38])).

tff(c_58,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_87046,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_87029,c_58])).

tff(c_87053,plain,
    ( ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1564,c_66957,c_87046])).

tff(c_87054,plain,(
    ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_87053])).

tff(c_87060,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_87054])).

tff(c_87070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_87060])).

tff(c_87071,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_87764,plain,(
    ! [C_2014,A_2015,B_2016] :
      ( m1_connsp_2(C_2014,A_2015,B_2016)
      | ~ m1_subset_1(C_2014,u1_struct_0(k9_yellow_6(A_2015,B_2016)))
      | ~ m1_subset_1(B_2016,u1_struct_0(A_2015))
      | ~ l1_pre_topc(A_2015)
      | ~ v2_pre_topc(A_2015)
      | v2_struct_0(A_2015) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_87774,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_87764])).

tff(c_87782,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_87774])).

tff(c_87783,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_87782])).

tff(c_87791,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_87783,c_46])).

tff(c_87794,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_87791])).

tff(c_87795,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_87794])).

tff(c_88711,plain,(
    ! [C_2032,B_2033,A_2034] :
      ( r2_hidden(C_2032,B_2033)
      | ~ m1_connsp_2(B_2033,A_2034,C_2032)
      | ~ m1_subset_1(C_2032,u1_struct_0(A_2034))
      | ~ m1_subset_1(B_2033,k1_zfmisc_1(u1_struct_0(A_2034)))
      | ~ l1_pre_topc(A_2034)
      | ~ v2_pre_topc(A_2034)
      | v2_struct_0(A_2034) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_88713,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_87783,c_88711])).

tff(c_88718,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_87795,c_64,c_88713])).

tff(c_88719,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_88718])).

tff(c_30,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_87100,plain,(
    ! [C_1914,B_1915,A_1916] :
      ( ~ v1_xboole_0(C_1914)
      | ~ m1_subset_1(B_1915,k1_zfmisc_1(C_1914))
      | ~ r2_hidden(A_1916,B_1915) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87107,plain,(
    ! [A_12,A_1916] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_1916,A_12) ) ),
    inference(resolution,[status(thm)],[c_71,c_87100])).

tff(c_88726,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_88719,c_87107])).

tff(c_88733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87071,c_88726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.22/15.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.71  
% 26.22/15.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.71  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 26.22/15.71  
% 26.22/15.71  %Foreground sorts:
% 26.22/15.71  
% 26.22/15.71  
% 26.22/15.71  %Background operators:
% 26.22/15.71  
% 26.22/15.71  
% 26.22/15.71  %Foreground operators:
% 26.22/15.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.22/15.71  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 26.22/15.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 26.22/15.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 26.22/15.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.22/15.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.22/15.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.22/15.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.22/15.71  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 26.22/15.71  tff('#skF_5', type, '#skF_5': $i).
% 26.22/15.71  tff('#skF_6', type, '#skF_6': $i).
% 26.22/15.71  tff('#skF_3', type, '#skF_3': $i).
% 26.22/15.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.22/15.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.22/15.71  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 26.22/15.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.22/15.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 26.22/15.71  tff('#skF_4', type, '#skF_4': $i).
% 26.22/15.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.22/15.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.22/15.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.22/15.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.22/15.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 26.22/15.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.22/15.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.22/15.71  
% 26.22/15.73  tff(f_180, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 26.22/15.73  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 26.22/15.73  tff(f_110, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 26.22/15.73  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 26.22/15.73  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 26.22/15.73  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 26.22/15.73  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 26.22/15.73  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 26.22/15.73  tff(f_96, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 26.22/15.73  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 26.22/15.73  tff(f_69, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 26.22/15.73  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 26.22/15.73  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 26.22/15.73  tff(f_82, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 26.22/15.73  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_474, plain, (![C_158, A_159, B_160]: (m1_connsp_2(C_158, A_159, B_160) | ~m1_subset_1(C_158, u1_struct_0(k9_yellow_6(A_159, B_160))) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.22/15.73  tff(c_484, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_474])).
% 26.22/15.73  tff(c_492, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_484])).
% 26.22/15.73  tff(c_493, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_492])).
% 26.22/15.73  tff(c_46, plain, (![C_33, A_30, B_31]: (m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_connsp_2(C_33, A_30, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 26.22/15.73  tff(c_501, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_493, c_46])).
% 26.22/15.73  tff(c_504, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_501])).
% 26.22/15.73  tff(c_505, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_504])).
% 26.22/15.73  tff(c_539, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, B_162) | ~m1_connsp_2(B_162, A_163, C_161) | ~m1_subset_1(C_161, u1_struct_0(A_163)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_127])).
% 26.22/15.73  tff(c_541, plain, (r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_493, c_539])).
% 26.22/15.73  tff(c_546, plain, (r2_hidden('#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_505, c_64, c_541])).
% 26.22/15.73  tff(c_547, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_546])).
% 26.22/15.73  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 26.22/15.73  tff(c_62, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_481, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_474])).
% 26.22/15.73  tff(c_488, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_481])).
% 26.22/15.73  tff(c_489, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_488])).
% 26.22/15.73  tff(c_495, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_489, c_46])).
% 26.22/15.73  tff(c_498, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_495])).
% 26.22/15.73  tff(c_499, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_498])).
% 26.22/15.73  tff(c_36, plain, (![A_16, B_17, C_18]: (k4_subset_1(A_16, B_17, C_18)=k2_xboole_0(B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 26.22/15.73  tff(c_1466, plain, (![B_181]: (k4_subset_1(u1_struct_0('#skF_3'), B_181, '#skF_6')=k2_xboole_0(B_181, '#skF_6') | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_505, c_36])).
% 26.22/15.73  tff(c_1518, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6')=k2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_499, c_1466])).
% 26.22/15.73  tff(c_34, plain, (![A_13, B_14, C_15]: (m1_subset_1(k4_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 26.22/15.73  tff(c_1560, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_34])).
% 26.22/15.73  tff(c_1564, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_505, c_1560])).
% 26.22/15.73  tff(c_83, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.22/15.73  tff(c_97, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_60, c_83])).
% 26.22/15.73  tff(c_120, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_97])).
% 26.22/15.73  tff(c_2254, plain, (![B_196, C_197, A_198]: (v3_pre_topc(k2_xboole_0(B_196, C_197), A_198) | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~v3_pre_topc(C_197, A_198) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_198))) | ~v3_pre_topc(B_196, A_198) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_96])).
% 26.22/15.73  tff(c_2284, plain, (![B_196]: (v3_pre_topc(k2_xboole_0(B_196, '#skF_5'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_196, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_499, c_2254])).
% 26.22/15.73  tff(c_2344, plain, (![B_196]: (v3_pre_topc(k2_xboole_0(B_196, '#skF_5'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_196, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2284])).
% 26.22/15.73  tff(c_45766, plain, (~v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2344])).
% 26.22/15.73  tff(c_24, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.22/15.73  tff(c_1641, plain, (![C_183, A_184, B_185]: (v3_pre_topc(C_183, A_184) | ~r2_hidden(C_183, u1_struct_0(k9_yellow_6(A_184, B_185))) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_146])).
% 26.22/15.73  tff(c_66722, plain, (![B_1468, A_1469, B_1470]: (v3_pre_topc(B_1468, A_1469) | ~m1_subset_1(B_1468, k1_zfmisc_1(u1_struct_0(A_1469))) | ~m1_subset_1(B_1470, u1_struct_0(A_1469)) | ~l1_pre_topc(A_1469) | ~v2_pre_topc(A_1469) | v2_struct_0(A_1469) | ~m1_subset_1(B_1468, u1_struct_0(k9_yellow_6(A_1469, B_1470))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1469, B_1470))))), inference(resolution, [status(thm)], [c_24, c_1641])).
% 26.22/15.73  tff(c_66796, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_62, c_66722])).
% 26.22/15.73  tff(c_66820, plain, (v3_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_499, c_66796])).
% 26.22/15.73  tff(c_66822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_70, c_45766, c_66820])).
% 26.22/15.73  tff(c_66824, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_2344])).
% 26.22/15.73  tff(c_2282, plain, (![B_196]: (v3_pre_topc(k2_xboole_0(B_196, '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_196, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_505, c_2254])).
% 26.22/15.73  tff(c_2341, plain, (![B_196]: (v3_pre_topc(k2_xboole_0(B_196, '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_196, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2282])).
% 26.22/15.73  tff(c_4002, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_2341])).
% 26.22/15.73  tff(c_45569, plain, (![B_1051, A_1052, B_1053]: (v3_pre_topc(B_1051, A_1052) | ~m1_subset_1(B_1051, k1_zfmisc_1(u1_struct_0(A_1052))) | ~m1_subset_1(B_1053, u1_struct_0(A_1052)) | ~l1_pre_topc(A_1052) | ~v2_pre_topc(A_1052) | v2_struct_0(A_1052) | ~m1_subset_1(B_1051, u1_struct_0(k9_yellow_6(A_1052, B_1053))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1052, B_1053))))), inference(resolution, [status(thm)], [c_24, c_1641])).
% 26.22/15.73  tff(c_45646, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_60, c_45569])).
% 26.22/15.73  tff(c_45671, plain, (v3_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_505, c_45646])).
% 26.22/15.73  tff(c_45673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_70, c_4002, c_45671])).
% 26.22/15.73  tff(c_66825, plain, (![B_1471]: (v3_pre_topc(k2_xboole_0(B_1471, '#skF_6'), '#skF_3') | ~m1_subset_1(B_1471, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_1471, '#skF_3'))), inference(splitRight, [status(thm)], [c_2341])).
% 26.22/15.73  tff(c_66906, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_499, c_66825])).
% 26.22/15.73  tff(c_66957, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66824, c_66906])).
% 26.22/15.73  tff(c_2926, plain, (![C_212, A_213, B_214]: (r2_hidden(C_212, u1_struct_0(k9_yellow_6(A_213, B_214))) | ~v3_pre_topc(C_212, A_213) | ~r2_hidden(B_214, C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(u1_struct_0(A_213))) | ~m1_subset_1(B_214, u1_struct_0(A_213)) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_146])).
% 26.22/15.73  tff(c_38, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 26.22/15.73  tff(c_87029, plain, (![C_1897, A_1898, B_1899]: (m1_subset_1(C_1897, u1_struct_0(k9_yellow_6(A_1898, B_1899))) | ~v3_pre_topc(C_1897, A_1898) | ~r2_hidden(B_1899, C_1897) | ~m1_subset_1(C_1897, k1_zfmisc_1(u1_struct_0(A_1898))) | ~m1_subset_1(B_1899, u1_struct_0(A_1898)) | ~l1_pre_topc(A_1898) | ~v2_pre_topc(A_1898) | v2_struct_0(A_1898))), inference(resolution, [status(thm)], [c_2926, c_38])).
% 26.22/15.73  tff(c_58, plain, (~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 26.22/15.73  tff(c_87046, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_87029, c_58])).
% 26.22/15.73  tff(c_87053, plain, (~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1564, c_66957, c_87046])).
% 26.22/15.73  tff(c_87054, plain, (~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_87053])).
% 26.22/15.73  tff(c_87060, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_4, c_87054])).
% 26.22/15.73  tff(c_87070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_547, c_87060])).
% 26.22/15.73  tff(c_87071, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_97])).
% 26.22/15.73  tff(c_87764, plain, (![C_2014, A_2015, B_2016]: (m1_connsp_2(C_2014, A_2015, B_2016) | ~m1_subset_1(C_2014, u1_struct_0(k9_yellow_6(A_2015, B_2016))) | ~m1_subset_1(B_2016, u1_struct_0(A_2015)) | ~l1_pre_topc(A_2015) | ~v2_pre_topc(A_2015) | v2_struct_0(A_2015))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.22/15.73  tff(c_87774, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_87764])).
% 26.22/15.73  tff(c_87782, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_87774])).
% 26.22/15.73  tff(c_87783, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_87782])).
% 26.22/15.73  tff(c_87791, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_87783, c_46])).
% 26.22/15.73  tff(c_87794, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_87791])).
% 26.22/15.73  tff(c_87795, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_87794])).
% 26.22/15.73  tff(c_88711, plain, (![C_2032, B_2033, A_2034]: (r2_hidden(C_2032, B_2033) | ~m1_connsp_2(B_2033, A_2034, C_2032) | ~m1_subset_1(C_2032, u1_struct_0(A_2034)) | ~m1_subset_1(B_2033, k1_zfmisc_1(u1_struct_0(A_2034))) | ~l1_pre_topc(A_2034) | ~v2_pre_topc(A_2034) | v2_struct_0(A_2034))), inference(cnfTransformation, [status(thm)], [f_127])).
% 26.22/15.73  tff(c_88713, plain, (r2_hidden('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_87783, c_88711])).
% 26.22/15.73  tff(c_88718, plain, (r2_hidden('#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_87795, c_64, c_88713])).
% 26.22/15.73  tff(c_88719, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_88718])).
% 26.22/15.73  tff(c_30, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.22/15.73  tff(c_32, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 26.22/15.73  tff(c_71, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 26.22/15.73  tff(c_87100, plain, (![C_1914, B_1915, A_1916]: (~v1_xboole_0(C_1914) | ~m1_subset_1(B_1915, k1_zfmisc_1(C_1914)) | ~r2_hidden(A_1916, B_1915))), inference(cnfTransformation, [status(thm)], [f_82])).
% 26.22/15.73  tff(c_87107, plain, (![A_12, A_1916]: (~v1_xboole_0(A_12) | ~r2_hidden(A_1916, A_12))), inference(resolution, [status(thm)], [c_71, c_87100])).
% 26.22/15.73  tff(c_88726, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_88719, c_87107])).
% 26.22/15.73  tff(c_88733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87071, c_88726])).
% 26.22/15.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.73  
% 26.22/15.73  Inference rules
% 26.22/15.73  ----------------------
% 26.22/15.73  #Ref     : 0
% 26.22/15.73  #Sup     : 19942
% 26.22/15.73  #Fact    : 18
% 26.22/15.73  #Define  : 0
% 26.22/15.73  #Split   : 48
% 26.22/15.73  #Chain   : 0
% 26.22/15.73  #Close   : 0
% 26.22/15.73  
% 26.22/15.73  Ordering : KBO
% 26.22/15.73  
% 26.22/15.73  Simplification rules
% 26.22/15.73  ----------------------
% 26.22/15.73  #Subsume      : 5817
% 26.22/15.73  #Demod        : 6357
% 26.22/15.73  #Tautology    : 1768
% 26.22/15.73  #SimpNegUnit  : 343
% 26.22/15.73  #BackRed      : 373
% 26.22/15.73  
% 26.22/15.73  #Partial instantiations: 0
% 26.22/15.74  #Strategies tried      : 1
% 26.22/15.74  
% 26.22/15.74  Timing (in seconds)
% 26.22/15.74  ----------------------
% 26.22/15.74  Preprocessing        : 0.35
% 26.22/15.74  Parsing              : 0.18
% 26.22/15.74  CNF conversion       : 0.03
% 26.22/15.74  Main loop            : 14.61
% 26.22/15.74  Inferencing          : 2.59
% 26.22/15.74  Reduction            : 4.57
% 26.22/15.74  Demodulation         : 3.51
% 26.22/15.74  BG Simplification    : 0.32
% 26.22/15.74  Subsumption          : 6.14
% 26.22/15.74  Abstraction          : 0.54
% 26.22/15.74  MUC search           : 0.00
% 26.22/15.74  Cooper               : 0.00
% 26.22/15.74  Total                : 15.01
% 26.22/15.74  Index Insertion      : 0.00
% 26.22/15.74  Index Deletion       : 0.00
% 26.22/15.74  Index Matching       : 0.00
% 26.22/15.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
