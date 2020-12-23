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
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 619 expanded)
%              Number of leaves         :   41 ( 250 expanded)
%              Depth                    :   16
%              Number of atoms          :  310 (2322 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
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

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_150,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_616,plain,(
    ! [C_174,A_175,B_176] :
      ( m1_connsp_2(C_174,A_175,B_176)
      | ~ m1_subset_1(C_174,u1_struct_0(k9_yellow_6(A_175,B_176)))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_630,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_616])).

tff(c_639,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_630])).

tff(c_640,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_639])).

tff(c_40,plain,(
    ! [C_37,A_34,B_35] :
      ( m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_connsp_2(C_37,A_34,B_35)
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_648,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_640,c_40])).

tff(c_651,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_648])).

tff(c_652,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_651])).

tff(c_674,plain,(
    ! [C_177,B_178,A_179] :
      ( r2_hidden(C_177,B_178)
      | ~ m1_connsp_2(B_178,A_179,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_179))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_676,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_640,c_674])).

tff(c_681,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_652,c_58,c_676])).

tff(c_682,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_681])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(k1_tarski(A_11),B_12) = B_12
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(A_92,C_93)
      | ~ r1_tarski(k2_xboole_0(A_92,B_94),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [A_92,B_94,B_9] : r1_tarski(A_92,k2_xboole_0(k2_xboole_0(A_92,B_94),B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_175])).

tff(c_10,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    ! [A_89,C_90,B_91] :
      ( r2_hidden(A_89,C_90)
      | ~ r1_tarski(k2_tarski(A_89,B_91),C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_329,plain,(
    ! [A_120,C_121] :
      ( r2_hidden(A_120,C_121)
      | ~ r1_tarski(k1_tarski(A_120),C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_161])).

tff(c_567,plain,(
    ! [A_158,B_159,B_160] : r2_hidden(A_158,k2_xboole_0(k2_xboole_0(k1_tarski(A_158),B_159),B_160)) ),
    inference(resolution,[status(thm)],[c_188,c_329])).

tff(c_576,plain,(
    ! [A_11,B_12,B_160] :
      ( r2_hidden(A_11,k2_xboole_0(B_12,B_160))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_567])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_627,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_616])).

tff(c_635,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_627])).

tff(c_636,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_635])).

tff(c_642,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_636,c_40])).

tff(c_645,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_642])).

tff(c_646,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_645])).

tff(c_32,plain,(
    ! [A_23,B_24,C_25] :
      ( k4_subset_1(A_23,B_24,C_25) = k2_xboole_0(B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_736,plain,(
    ! [B_187] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_187,'#skF_5') = k2_xboole_0(B_187,'#skF_5')
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_646,c_32])).

tff(c_755,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_652,c_736])).

tff(c_30,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k4_subset_1(A_20,B_21,C_22),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_919,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_30])).

tff(c_923,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_646,c_919])).

tff(c_1090,plain,(
    ! [C_216,A_217,B_218] :
      ( r2_hidden(C_216,u1_struct_0(k9_yellow_6(A_217,B_218)))
      | ~ v3_pre_topc(C_216,A_217)
      | ~ r2_hidden(B_218,C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2259,plain,(
    ! [C_341,A_342,B_343] :
      ( m1_subset_1(C_341,u1_struct_0(k9_yellow_6(A_342,B_343)))
      | ~ v3_pre_topc(C_341,A_342)
      | ~ r2_hidden(B_343,C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_subset_1(B_343,u1_struct_0(A_342))
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_1090,c_34])).

tff(c_52,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2265,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2259,c_52])).

tff(c_2272,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_923,c_2265])).

tff(c_2273,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2272])).

tff(c_2293,plain,(
    ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2273])).

tff(c_2296,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_576,c_2293])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_2296])).

tff(c_2304,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2273])).

tff(c_120,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,A_85)
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_54,c_120])).

tff(c_151,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_717,plain,(
    ! [C_181,A_182,B_183] :
      ( v3_pre_topc(C_181,A_182)
      | ~ r2_hidden(C_181,u1_struct_0(k9_yellow_6(A_182,B_183)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2467,plain,(
    ! [B_349,A_350,B_351] :
      ( v3_pre_topc(B_349,A_350)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ m1_subset_1(B_351,u1_struct_0(A_350))
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350)
      | ~ m1_subset_1(B_349,u1_struct_0(k9_yellow_6(A_350,B_351)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_350,B_351))) ) ),
    inference(resolution,[status(thm)],[c_24,c_717])).

tff(c_2484,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_56,c_2467])).

tff(c_2494,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_652,c_2484])).

tff(c_2495,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_64,c_2494])).

tff(c_2481,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_54,c_2467])).

tff(c_2490,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_646,c_2481])).

tff(c_2491,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_64,c_2490])).

tff(c_925,plain,(
    ! [B_207,C_208,A_209] :
      ( v3_pre_topc(k2_xboole_0(B_207,C_208),A_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ v3_pre_topc(C_208,A_209)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ v3_pre_topc(B_207,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_931,plain,(
    ! [B_207] :
      ( v3_pre_topc(k2_xboole_0(B_207,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_207,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_646,c_925])).

tff(c_949,plain,(
    ! [B_207] :
      ( v3_pre_topc(k2_xboole_0(B_207,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_931])).

tff(c_2810,plain,(
    ! [B_356] :
      ( v3_pre_topc(k2_xboole_0(B_356,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_356,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_949])).

tff(c_2849,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_652,c_2810])).

tff(c_2883,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2495,c_2849])).

tff(c_2885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2304,c_2883])).

tff(c_2887,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_2889,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2887,c_139])).

tff(c_3356,plain,(
    ! [C_444,A_445,B_446] :
      ( m1_connsp_2(C_444,A_445,B_446)
      | ~ m1_subset_1(C_444,u1_struct_0(k9_yellow_6(A_445,B_446)))
      | ~ m1_subset_1(B_446,u1_struct_0(A_445))
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3370,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_3356])).

tff(c_3379,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_3370])).

tff(c_3380,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3379])).

tff(c_3388,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3380,c_40])).

tff(c_3391,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_3388])).

tff(c_3392,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3391])).

tff(c_3420,plain,(
    ! [C_448,B_449,A_450] :
      ( r2_hidden(C_448,B_449)
      | ~ m1_connsp_2(B_449,A_450,C_448)
      | ~ m1_subset_1(C_448,u1_struct_0(A_450))
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ l1_pre_topc(A_450)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3422,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3380,c_3420])).

tff(c_3427,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3392,c_58,c_3422])).

tff(c_3428,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3427])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3438,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3428,c_2])).

tff(c_3443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2889,c_3438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.14  
% 5.82/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.14  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.82/2.14  
% 5.82/2.14  %Foreground sorts:
% 5.82/2.14  
% 5.82/2.14  
% 5.82/2.14  %Background operators:
% 5.82/2.14  
% 5.82/2.14  
% 5.82/2.14  %Foreground operators:
% 5.82/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.82/2.14  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.82/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.82/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.82/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.82/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.82/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.82/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.82/2.14  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.82/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.82/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.82/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.82/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.82/2.14  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.82/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.82/2.14  tff('#skF_4', type, '#skF_4': $i).
% 5.82/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.82/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.82/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.82/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.82/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.82/2.14  
% 5.82/2.16  tff(f_184, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.82/2.16  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 5.82/2.16  tff(f_114, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.82/2.16  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.82/2.16  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 5.82/2.16  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.82/2.16  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.82/2.16  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.82/2.16  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.82/2.16  tff(f_76, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.82/2.16  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.82/2.16  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.82/2.16  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.82/2.16  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.82/2.16  tff(f_100, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.82/2.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.82/2.16  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_616, plain, (![C_174, A_175, B_176]: (m1_connsp_2(C_174, A_175, B_176) | ~m1_subset_1(C_174, u1_struct_0(k9_yellow_6(A_175, B_176))) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.82/2.16  tff(c_630, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_616])).
% 5.82/2.16  tff(c_639, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_630])).
% 5.82/2.16  tff(c_640, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_639])).
% 5.82/2.16  tff(c_40, plain, (![C_37, A_34, B_35]: (m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_connsp_2(C_37, A_34, B_35) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.82/2.16  tff(c_648, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_640, c_40])).
% 5.82/2.16  tff(c_651, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_648])).
% 5.82/2.16  tff(c_652, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_651])).
% 5.82/2.16  tff(c_674, plain, (![C_177, B_178, A_179]: (r2_hidden(C_177, B_178) | ~m1_connsp_2(B_178, A_179, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_179)) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.82/2.16  tff(c_676, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_640, c_674])).
% 5.82/2.16  tff(c_681, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_652, c_58, c_676])).
% 5.82/2.16  tff(c_682, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_681])).
% 5.82/2.16  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), B_12)=B_12 | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.82/2.16  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.82/2.16  tff(c_175, plain, (![A_92, C_93, B_94]: (r1_tarski(A_92, C_93) | ~r1_tarski(k2_xboole_0(A_92, B_94), C_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.82/2.16  tff(c_188, plain, (![A_92, B_94, B_9]: (r1_tarski(A_92, k2_xboole_0(k2_xboole_0(A_92, B_94), B_9)))), inference(resolution, [status(thm)], [c_8, c_175])).
% 5.82/2.16  tff(c_10, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.82/2.16  tff(c_161, plain, (![A_89, C_90, B_91]: (r2_hidden(A_89, C_90) | ~r1_tarski(k2_tarski(A_89, B_91), C_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.82/2.16  tff(c_329, plain, (![A_120, C_121]: (r2_hidden(A_120, C_121) | ~r1_tarski(k1_tarski(A_120), C_121))), inference(superposition, [status(thm), theory('equality')], [c_10, c_161])).
% 5.82/2.16  tff(c_567, plain, (![A_158, B_159, B_160]: (r2_hidden(A_158, k2_xboole_0(k2_xboole_0(k1_tarski(A_158), B_159), B_160)))), inference(resolution, [status(thm)], [c_188, c_329])).
% 5.82/2.16  tff(c_576, plain, (![A_11, B_12, B_160]: (r2_hidden(A_11, k2_xboole_0(B_12, B_160)) | ~r2_hidden(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_567])).
% 5.82/2.16  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.16  tff(c_627, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_616])).
% 5.82/2.16  tff(c_635, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_627])).
% 5.82/2.16  tff(c_636, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_635])).
% 5.82/2.16  tff(c_642, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_636, c_40])).
% 5.82/2.16  tff(c_645, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_642])).
% 5.82/2.16  tff(c_646, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_645])).
% 5.82/2.16  tff(c_32, plain, (![A_23, B_24, C_25]: (k4_subset_1(A_23, B_24, C_25)=k2_xboole_0(B_24, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.82/2.16  tff(c_736, plain, (![B_187]: (k4_subset_1(u1_struct_0('#skF_2'), B_187, '#skF_5')=k2_xboole_0(B_187, '#skF_5') | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_646, c_32])).
% 5.82/2.16  tff(c_755, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_652, c_736])).
% 5.82/2.16  tff(c_30, plain, (![A_20, B_21, C_22]: (m1_subset_1(k4_subset_1(A_20, B_21, C_22), k1_zfmisc_1(A_20)) | ~m1_subset_1(C_22, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.82/2.17  tff(c_919, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_755, c_30])).
% 5.82/2.17  tff(c_923, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_646, c_919])).
% 5.82/2.17  tff(c_1090, plain, (![C_216, A_217, B_218]: (r2_hidden(C_216, u1_struct_0(k9_yellow_6(A_217, B_218))) | ~v3_pre_topc(C_216, A_217) | ~r2_hidden(B_218, C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.82/2.17  tff(c_34, plain, (![A_26, B_27]: (m1_subset_1(A_26, B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.82/2.17  tff(c_2259, plain, (![C_341, A_342, B_343]: (m1_subset_1(C_341, u1_struct_0(k9_yellow_6(A_342, B_343))) | ~v3_pre_topc(C_341, A_342) | ~r2_hidden(B_343, C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_subset_1(B_343, u1_struct_0(A_342)) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(resolution, [status(thm)], [c_1090, c_34])).
% 5.82/2.17  tff(c_52, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.82/2.17  tff(c_2265, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2259, c_52])).
% 5.82/2.17  tff(c_2272, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_923, c_2265])).
% 5.82/2.17  tff(c_2273, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2272])).
% 5.82/2.17  tff(c_2293, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2273])).
% 5.82/2.17  tff(c_2296, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_576, c_2293])).
% 5.82/2.17  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_682, c_2296])).
% 5.82/2.17  tff(c_2304, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_2273])).
% 5.82/2.17  tff(c_120, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, A_85) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.82/2.17  tff(c_138, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_54, c_120])).
% 5.82/2.17  tff(c_151, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_138])).
% 5.82/2.17  tff(c_24, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.82/2.17  tff(c_717, plain, (![C_181, A_182, B_183]: (v3_pre_topc(C_181, A_182) | ~r2_hidden(C_181, u1_struct_0(k9_yellow_6(A_182, B_183))) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.82/2.17  tff(c_2467, plain, (![B_349, A_350, B_351]: (v3_pre_topc(B_349, A_350) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_350))) | ~m1_subset_1(B_351, u1_struct_0(A_350)) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350) | ~m1_subset_1(B_349, u1_struct_0(k9_yellow_6(A_350, B_351))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_350, B_351))))), inference(resolution, [status(thm)], [c_24, c_717])).
% 5.82/2.17  tff(c_2484, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_56, c_2467])).
% 5.82/2.17  tff(c_2494, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_652, c_2484])).
% 5.82/2.17  tff(c_2495, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_151, c_64, c_2494])).
% 5.82/2.17  tff(c_2481, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_54, c_2467])).
% 5.82/2.17  tff(c_2490, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_646, c_2481])).
% 5.82/2.17  tff(c_2491, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_151, c_64, c_2490])).
% 5.82/2.17  tff(c_925, plain, (![B_207, C_208, A_209]: (v3_pre_topc(k2_xboole_0(B_207, C_208), A_209) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~v3_pre_topc(C_208, A_209) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_209))) | ~v3_pre_topc(B_207, A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.82/2.17  tff(c_931, plain, (![B_207]: (v3_pre_topc(k2_xboole_0(B_207, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_207, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_646, c_925])).
% 5.82/2.17  tff(c_949, plain, (![B_207]: (v3_pre_topc(k2_xboole_0(B_207, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_931])).
% 5.82/2.17  tff(c_2810, plain, (![B_356]: (v3_pre_topc(k2_xboole_0(B_356, '#skF_5'), '#skF_2') | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_356, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_949])).
% 5.82/2.17  tff(c_2849, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_652, c_2810])).
% 5.82/2.17  tff(c_2883, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2495, c_2849])).
% 5.82/2.17  tff(c_2885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2304, c_2883])).
% 5.82/2.17  tff(c_2887, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_138])).
% 5.82/2.17  tff(c_139, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_56, c_120])).
% 5.82/2.17  tff(c_2889, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2887, c_139])).
% 5.82/2.17  tff(c_3356, plain, (![C_444, A_445, B_446]: (m1_connsp_2(C_444, A_445, B_446) | ~m1_subset_1(C_444, u1_struct_0(k9_yellow_6(A_445, B_446))) | ~m1_subset_1(B_446, u1_struct_0(A_445)) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.82/2.17  tff(c_3370, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_3356])).
% 5.82/2.17  tff(c_3379, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_3370])).
% 5.82/2.17  tff(c_3380, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_3379])).
% 5.82/2.17  tff(c_3388, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3380, c_40])).
% 5.82/2.17  tff(c_3391, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_3388])).
% 5.82/2.17  tff(c_3392, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_3391])).
% 5.82/2.17  tff(c_3420, plain, (![C_448, B_449, A_450]: (r2_hidden(C_448, B_449) | ~m1_connsp_2(B_449, A_450, C_448) | ~m1_subset_1(C_448, u1_struct_0(A_450)) | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0(A_450))) | ~l1_pre_topc(A_450) | ~v2_pre_topc(A_450) | v2_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.82/2.17  tff(c_3422, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3380, c_3420])).
% 5.82/2.17  tff(c_3427, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3392, c_58, c_3422])).
% 5.82/2.17  tff(c_3428, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_3427])).
% 5.82/2.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.82/2.17  tff(c_3438, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3428, c_2])).
% 5.82/2.17  tff(c_3443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2889, c_3438])).
% 5.82/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.17  
% 5.82/2.17  Inference rules
% 5.82/2.17  ----------------------
% 5.82/2.17  #Ref     : 0
% 5.82/2.17  #Sup     : 774
% 5.82/2.17  #Fact    : 0
% 5.82/2.17  #Define  : 0
% 5.82/2.17  #Split   : 4
% 5.82/2.17  #Chain   : 0
% 5.82/2.17  #Close   : 0
% 5.82/2.17  
% 5.82/2.17  Ordering : KBO
% 5.82/2.17  
% 5.82/2.17  Simplification rules
% 5.82/2.17  ----------------------
% 5.82/2.17  #Subsume      : 161
% 5.82/2.17  #Demod        : 357
% 5.82/2.17  #Tautology    : 164
% 5.82/2.17  #SimpNegUnit  : 22
% 5.82/2.17  #BackRed      : 0
% 5.82/2.17  
% 5.82/2.17  #Partial instantiations: 0
% 5.82/2.17  #Strategies tried      : 1
% 5.82/2.17  
% 5.82/2.17  Timing (in seconds)
% 5.82/2.17  ----------------------
% 6.05/2.17  Preprocessing        : 0.37
% 6.05/2.17  Parsing              : 0.20
% 6.05/2.17  CNF conversion       : 0.03
% 6.05/2.17  Main loop            : 1.02
% 6.05/2.17  Inferencing          : 0.34
% 6.05/2.17  Reduction            : 0.39
% 6.05/2.17  Demodulation         : 0.29
% 6.05/2.17  BG Simplification    : 0.04
% 6.05/2.17  Subsumption          : 0.18
% 6.05/2.17  Abstraction          : 0.04
% 6.05/2.17  MUC search           : 0.00
% 6.05/2.17  Cooper               : 0.00
% 6.05/2.17  Total                : 1.44
% 6.05/2.17  Index Insertion      : 0.00
% 6.05/2.17  Index Deletion       : 0.00
% 6.05/2.17  Index Matching       : 0.00
% 6.05/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
