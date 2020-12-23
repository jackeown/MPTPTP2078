%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 142 expanded)
%              Number of leaves         :   42 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 ( 319 expanded)
%              Number of equality atoms :   22 (  65 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_67,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_105,axiom,(
    ! [A] :
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_86,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_110,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_110])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113])).

tff(c_119,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_118])).

tff(c_18,plain,(
    ! [A_15] : k9_setfam_1(A_15) = k1_zfmisc_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_19] : u1_struct_0(k3_yellow_1(A_19)) = k9_setfam_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_47,plain,(
    v1_subset_1('#skF_3',k9_setfam_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_52,plain,(
    v1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_38,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_40] :
      ( v1_xboole_0(A_40)
      | r2_hidden('#skF_1'(A_40),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,'#skF_1'(A_41))
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_91,c_16])).

tff(c_109,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,k1_tarski(B_9)) = A_8
      | r2_hidden(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_144,plain,(
    ! [A_50,B_51,C_52] :
      ( k7_subset_1(A_50,B_51,C_52) = k4_xboole_0(B_51,C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [C_52] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_2')),'#skF_3',C_52) = k4_xboole_0('#skF_3',C_52) ),
    inference(resolution,[status(thm)],[c_53,c_144])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_20))),B_22,k1_tarski(k1_xboole_0)) = k2_yellow19(A_20,k3_yellow19(A_20,k2_struct_0(A_20),B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_20)))))
      | ~ v13_waybel_0(B_22,k3_yellow_1(k2_struct_0(A_20)))
      | ~ v2_waybel_0(B_22,k3_yellow_1(k2_struct_0(A_20)))
      | v1_xboole_0(B_22)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_20,B_22] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_20)),B_22,k1_tarski(k1_xboole_0)) = k2_yellow19(A_20,k3_yellow19(A_20,k2_struct_0(A_20),B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_20))))
      | ~ v13_waybel_0(B_22,k3_yellow_1(k2_struct_0(A_20)))
      | ~ v2_waybel_0(B_22,k3_yellow_1(k2_struct_0(A_20)))
      | v1_xboole_0(B_22)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_28])).

tff(c_169,plain,(
    ! [A_59,B_60] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_59)),B_60,k1_tarski(k1_xboole_0)) = k2_yellow19(A_59,k3_yellow19(A_59,k2_struct_0(A_59),B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_59))))
      | ~ v13_waybel_0(B_60,k3_yellow_1(k2_struct_0(A_59)))
      | ~ v2_waybel_0(B_60,k3_yellow_1(k2_struct_0(A_59)))
      | v1_xboole_0(B_60)
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_50])).

tff(c_171,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_2')),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_169])).

tff(c_174,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_147,c_171])).

tff(c_175,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_174])).

tff(c_32,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_176,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_32])).

tff(c_184,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_30,plain,(
    ! [C_29,B_27,A_23] :
      ( ~ v1_xboole_0(C_29)
      | ~ r2_hidden(C_29,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_23))))
      | ~ v13_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v2_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v1_subset_1(B_27,u1_struct_0(k3_yellow_1(A_23)))
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_49,plain,(
    ! [C_29,B_27,A_23] :
      ( ~ v1_xboole_0(C_29)
      | ~ r2_hidden(C_29,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k9_setfam_1(A_23)))
      | ~ v13_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v2_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v1_subset_1(B_27,k9_setfam_1(A_23))
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_30])).

tff(c_54,plain,(
    ! [C_29,B_27,A_23] :
      ( ~ v1_xboole_0(C_29)
      | ~ r2_hidden(C_29,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_23)))
      | ~ v13_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v2_waybel_0(B_27,k3_yellow_1(A_23))
      | ~ v1_subset_1(B_27,k1_zfmisc_1(A_23))
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_49])).

tff(c_186,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_23)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_23))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_23))
      | ~ v1_subset_1('#skF_3',k1_zfmisc_1(A_23))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_184,c_54])).

tff(c_195,plain,(
    ! [A_23] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_23)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_23))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_23))
      | ~ v1_subset_1('#skF_3',k1_zfmisc_1(A_23))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_186])).

tff(c_199,plain,(
    ! [A_61] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_61)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_61))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_61))
      | ~ v1_subset_1('#skF_3',k1_zfmisc_1(A_61))
      | v1_xboole_0(A_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_195])).

tff(c_202,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_53,c_199])).

tff(c_205,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_38,c_36,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:08:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.25  
% 2.25/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.26  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.25/1.26  
% 2.25/1.26  %Foreground sorts:
% 2.25/1.26  
% 2.25/1.26  
% 2.25/1.26  %Background operators:
% 2.25/1.26  
% 2.25/1.26  
% 2.25/1.26  %Foreground operators:
% 2.25/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.26  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.25/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.25/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.26  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.25/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.26  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.25/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.26  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.25/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.26  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.25/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.26  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.25/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.25/1.26  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.26  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.25/1.26  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.25/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.25/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.26  
% 2.25/1.27  tff(f_125, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.25/1.27  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.25/1.27  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.25/1.27  tff(f_51, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.25/1.27  tff(f_67, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 2.25/1.27  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.25/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.25/1.27  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.25/1.27  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.25/1.27  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.25/1.27  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.25/1.27  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.25/1.27  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_86, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.27  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_86])).
% 2.25/1.27  tff(c_110, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.25/1.27  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_110])).
% 2.25/1.27  tff(c_118, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113])).
% 2.25/1.27  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_118])).
% 2.25/1.27  tff(c_18, plain, (![A_15]: (k9_setfam_1(A_15)=k1_zfmisc_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.27  tff(c_26, plain, (![A_19]: (u1_struct_0(k3_yellow_1(A_19))=k9_setfam_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.27  tff(c_40, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_47, plain, (v1_subset_1('#skF_3', k9_setfam_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40])).
% 2.25/1.27  tff(c_52, plain, (v1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_47])).
% 2.25/1.27  tff(c_38, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_36, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 2.25/1.27  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48])).
% 2.25/1.27  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.27  tff(c_91, plain, (![A_40]: (v1_xboole_0(A_40) | r2_hidden('#skF_1'(A_40), A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.27  tff(c_16, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.27  tff(c_104, plain, (![A_41]: (~r1_tarski(A_41, '#skF_1'(A_41)) | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_91, c_16])).
% 2.25/1.27  tff(c_109, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.25/1.27  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k1_tarski(B_9))=A_8 | r2_hidden(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.27  tff(c_144, plain, (![A_50, B_51, C_52]: (k7_subset_1(A_50, B_51, C_52)=k4_xboole_0(B_51, C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.27  tff(c_147, plain, (![C_52]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_2')), '#skF_3', C_52)=k4_xboole_0('#skF_3', C_52))), inference(resolution, [status(thm)], [c_53, c_144])).
% 2.25/1.27  tff(c_28, plain, (![A_20, B_22]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_20))), B_22, k1_tarski(k1_xboole_0))=k2_yellow19(A_20, k3_yellow19(A_20, k2_struct_0(A_20), B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_20))))) | ~v13_waybel_0(B_22, k3_yellow_1(k2_struct_0(A_20))) | ~v2_waybel_0(B_22, k3_yellow_1(k2_struct_0(A_20))) | v1_xboole_0(B_22) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.25/1.27  tff(c_50, plain, (![A_20, B_22]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_20)), B_22, k1_tarski(k1_xboole_0))=k2_yellow19(A_20, k3_yellow19(A_20, k2_struct_0(A_20), B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_20)))) | ~v13_waybel_0(B_22, k3_yellow_1(k2_struct_0(A_20))) | ~v2_waybel_0(B_22, k3_yellow_1(k2_struct_0(A_20))) | v1_xboole_0(B_22) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_28])).
% 2.25/1.27  tff(c_169, plain, (![A_59, B_60]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_59)), B_60, k1_tarski(k1_xboole_0))=k2_yellow19(A_59, k3_yellow19(A_59, k2_struct_0(A_59), B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_59)))) | ~v13_waybel_0(B_60, k3_yellow_1(k2_struct_0(A_59))) | ~v2_waybel_0(B_60, k3_yellow_1(k2_struct_0(A_59))) | v1_xboole_0(B_60) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_50])).
% 2.25/1.27  tff(c_171, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_2')), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_53, c_169])).
% 2.25/1.27  tff(c_174, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_147, c_171])).
% 2.25/1.27  tff(c_175, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_174])).
% 2.25/1.27  tff(c_32, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.25/1.27  tff(c_176, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_32])).
% 2.25/1.27  tff(c_184, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 2.25/1.27  tff(c_30, plain, (![C_29, B_27, A_23]: (~v1_xboole_0(C_29) | ~r2_hidden(C_29, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_23)))) | ~v13_waybel_0(B_27, k3_yellow_1(A_23)) | ~v2_waybel_0(B_27, k3_yellow_1(A_23)) | ~v1_subset_1(B_27, u1_struct_0(k3_yellow_1(A_23))) | v1_xboole_0(B_27) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.25/1.27  tff(c_49, plain, (![C_29, B_27, A_23]: (~v1_xboole_0(C_29) | ~r2_hidden(C_29, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(k9_setfam_1(A_23))) | ~v13_waybel_0(B_27, k3_yellow_1(A_23)) | ~v2_waybel_0(B_27, k3_yellow_1(A_23)) | ~v1_subset_1(B_27, k9_setfam_1(A_23)) | v1_xboole_0(B_27) | v1_xboole_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_30])).
% 2.25/1.27  tff(c_54, plain, (![C_29, B_27, A_23]: (~v1_xboole_0(C_29) | ~r2_hidden(C_29, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_23))) | ~v13_waybel_0(B_27, k3_yellow_1(A_23)) | ~v2_waybel_0(B_27, k3_yellow_1(A_23)) | ~v1_subset_1(B_27, k1_zfmisc_1(A_23)) | v1_xboole_0(B_27) | v1_xboole_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_49])).
% 2.25/1.27  tff(c_186, plain, (![A_23]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_23))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_23)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_23)) | ~v1_subset_1('#skF_3', k1_zfmisc_1(A_23)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_184, c_54])).
% 2.25/1.27  tff(c_195, plain, (![A_23]: (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_23))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_23)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_23)) | ~v1_subset_1('#skF_3', k1_zfmisc_1(A_23)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_186])).
% 2.25/1.27  tff(c_199, plain, (![A_61]: (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_61))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_61)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_61)) | ~v1_subset_1('#skF_3', k1_zfmisc_1(A_61)) | v1_xboole_0(A_61))), inference(negUnitSimplification, [status(thm)], [c_42, c_195])).
% 2.25/1.27  tff(c_202, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_53, c_199])).
% 2.25/1.27  tff(c_205, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_38, c_36, c_202])).
% 2.25/1.27  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_205])).
% 2.25/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  Inference rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Ref     : 0
% 2.25/1.27  #Sup     : 32
% 2.25/1.27  #Fact    : 0
% 2.25/1.27  #Define  : 0
% 2.25/1.27  #Split   : 0
% 2.25/1.27  #Chain   : 0
% 2.25/1.27  #Close   : 0
% 2.25/1.27  
% 2.25/1.27  Ordering : KBO
% 2.25/1.27  
% 2.25/1.27  Simplification rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Subsume      : 1
% 2.25/1.27  #Demod        : 26
% 2.25/1.27  #Tautology    : 18
% 2.25/1.27  #SimpNegUnit  : 5
% 2.25/1.27  #BackRed      : 1
% 2.25/1.27  
% 2.25/1.27  #Partial instantiations: 0
% 2.25/1.27  #Strategies tried      : 1
% 2.25/1.27  
% 2.25/1.27  Timing (in seconds)
% 2.25/1.27  ----------------------
% 2.25/1.28  Preprocessing        : 0.33
% 2.25/1.28  Parsing              : 0.18
% 2.25/1.28  CNF conversion       : 0.02
% 2.25/1.28  Main loop            : 0.18
% 2.25/1.28  Inferencing          : 0.07
% 2.25/1.28  Reduction            : 0.07
% 2.25/1.28  Demodulation         : 0.05
% 2.25/1.28  BG Simplification    : 0.02
% 2.25/1.28  Subsumption          : 0.02
% 2.25/1.28  Abstraction          : 0.01
% 2.25/1.28  MUC search           : 0.00
% 2.25/1.28  Cooper               : 0.00
% 2.25/1.28  Total                : 0.55
% 2.25/1.28  Index Insertion      : 0.00
% 2.25/1.28  Index Deletion       : 0.00
% 2.25/1.28  Index Matching       : 0.00
% 2.25/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
