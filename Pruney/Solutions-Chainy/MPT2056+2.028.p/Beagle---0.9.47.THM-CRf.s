%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.68s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 249 expanded)
%              Number of leaves         :   47 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  221 ( 580 expanded)
%              Number of equality atoms :   49 ( 150 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_86,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_42,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_155,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_159,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_155])).

tff(c_164,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_167,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_164])).

tff(c_172,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_167])).

tff(c_173,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_172])).

tff(c_46,plain,(
    ! [A_26] : k9_setfam_1(A_26) = k1_zfmisc_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_30] : u1_struct_0(k3_yellow_1(A_30)) = k9_setfam_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_75,plain,(
    v1_subset_1('#skF_5',k9_setfam_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_80,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75])).

tff(c_66,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_81,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_320,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_323,plain,(
    ! [C_76] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',C_76) = k4_xboole_0('#skF_5',C_76) ),
    inference(resolution,[status(thm)],[c_81,c_320])).

tff(c_56,plain,(
    ! [A_31,B_33] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))),B_33,k1_tarski(k1_xboole_0)) = k2_yellow19(A_31,k3_yellow19(A_31,k2_struct_0(A_31),B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31)))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | ~ v2_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | v1_xboole_0(B_33)
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_78,plain,(
    ! [A_31,B_33] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_31)),B_33,k1_tarski(k1_xboole_0)) = k2_yellow19(A_31,k3_yellow19(A_31,k2_struct_0(A_31),B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_31))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | ~ v2_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_31)))
      | v1_xboole_0(B_33)
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_56])).

tff(c_1827,plain,(
    ! [A_172,B_173] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_172)),B_173,k1_tarski(k1_xboole_0)) = k2_yellow19(A_172,k3_yellow19(A_172,k2_struct_0(A_172),B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_172))))
      | ~ v13_waybel_0(B_173,k3_yellow_1(k2_struct_0(A_172)))
      | ~ v2_waybel_0(B_173,k3_yellow_1(k2_struct_0(A_172)))
      | v1_xboole_0(B_173)
      | ~ l1_struct_0(A_172)
      | v2_struct_0(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_78])).

tff(c_1829,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_1827])).

tff(c_1832,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_64,c_323,c_1829])).

tff(c_1833,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_1832])).

tff(c_60,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1872,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_60])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_906,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r2_hidden('#skF_2'(A_130,B_131,C_132),C_132)
      | r2_hidden('#skF_3'(A_130,B_131,C_132),C_132)
      | k4_xboole_0(A_130,B_131) = C_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_919,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_3'(A_5,B_6,A_5),A_5)
      | k4_xboole_0(A_5,B_6) = A_5 ) ),
    inference(resolution,[status(thm)],[c_22,c_906])).

tff(c_1269,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_2'(A_149,B_150,C_151),A_149)
      | r2_hidden('#skF_3'(A_149,B_150,C_151),B_150)
      | ~ r2_hidden('#skF_3'(A_149,B_150,C_151),A_149)
      | k4_xboole_0(A_149,B_150) = C_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),A_5)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3632,plain,(
    ! [A_257,B_258] :
      ( r2_hidden('#skF_3'(A_257,B_258,A_257),B_258)
      | ~ r2_hidden('#skF_3'(A_257,B_258,A_257),A_257)
      | k4_xboole_0(A_257,B_258) = A_257 ) ),
    inference(resolution,[status(thm)],[c_1269,c_12])).

tff(c_3669,plain,(
    ! [A_259,B_260] :
      ( r2_hidden('#skF_3'(A_259,B_260,A_259),B_260)
      | k4_xboole_0(A_259,B_260) = A_259 ) ),
    inference(resolution,[status(thm)],[c_919,c_3632])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [C_50,B_51] : ~ r2_hidden(C_50,k4_xboole_0(B_51,k1_tarski(C_50))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_206,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_180])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [D_60,A_61,B_62] :
      ( r2_hidden(D_60,A_61)
      | ~ r2_hidden(D_60,k4_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_224,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_61,B_62)),A_61)
      | v1_xboole_0(k4_xboole_0(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_292,plain,(
    ! [D_68,B_69,A_70] :
      ( ~ r2_hidden(D_68,B_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1428,plain,(
    ! [A_159,B_160] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_159,B_160)),B_160)
      | v1_xboole_0(k4_xboole_0(A_159,B_160)) ) ),
    inference(resolution,[status(thm)],[c_4,c_292])).

tff(c_1446,plain,(
    ! [A_61] : v1_xboole_0(k4_xboole_0(A_61,A_61)) ),
    inference(resolution,[status(thm)],[c_224,c_1428])).

tff(c_1475,plain,(
    ! [A_161] : v1_xboole_0(k3_xboole_0(A_161,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_1446])).

tff(c_696,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_2'(A_117,B_118,C_119),A_117)
      | r2_hidden('#skF_3'(A_117,B_118,C_119),C_119)
      | k4_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_728,plain,(
    ! [B_118,C_119] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_118,C_119),C_119)
      | k4_xboole_0(k1_xboole_0,B_118) = C_119 ) ),
    inference(resolution,[status(thm)],[c_696,c_142])).

tff(c_782,plain,(
    ! [B_120,C_121] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_120,C_121),C_121)
      | k1_xboole_0 = C_121 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_728])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_824,plain,(
    ! [C_121] :
      ( ~ v1_xboole_0(C_121)
      | k1_xboole_0 = C_121 ) ),
    inference(resolution,[status(thm)],[c_782,c_2])).

tff(c_1494,plain,(
    ! [A_161] : k3_xboole_0(A_161,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1475,c_824])).

tff(c_1657,plain,(
    ! [A_167] : k4_xboole_0(A_167,A_167) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_206])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(A_20,k4_xboole_0(B_21,k1_tarski(C_22)))
      | C_22 = A_20
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1688,plain,(
    ! [A_20,C_22] :
      ( r2_hidden(A_20,k1_xboole_0)
      | C_22 = A_20
      | ~ r2_hidden(A_20,k1_tarski(C_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_38])).

tff(c_1743,plain,(
    ! [C_22,A_20] :
      ( C_22 = A_20
      | ~ r2_hidden(A_20,k1_tarski(C_22)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1688])).

tff(c_22209,plain,(
    ! [A_564,C_565] :
      ( '#skF_3'(A_564,k1_tarski(C_565),A_564) = C_565
      | k4_xboole_0(A_564,k1_tarski(C_565)) = A_564 ) ),
    inference(resolution,[status(thm)],[c_3669,c_1743])).

tff(c_22569,plain,(
    '#skF_3'('#skF_5',k1_tarski(k1_xboole_0),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22209,c_1872])).

tff(c_22594,plain,
    ( r2_hidden(k1_xboole_0,'#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_22569,c_919])).

tff(c_22609,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1872,c_22594])).

tff(c_58,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_77,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k9_setfam_1(A_34)))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,k9_setfam_1(A_34))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_58])).

tff(c_82,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,k1_zfmisc_1(A_34))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_77])).

tff(c_22616,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_34))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_22609,c_82])).

tff(c_22626,plain,(
    ! [A_34] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_34))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22616])).

tff(c_22883,plain,(
    ! [A_574] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_574)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_574))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_574))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_574))
      | v1_xboole_0(A_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_22626])).

tff(c_22886,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_81,c_22883])).

tff(c_22889,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_64,c_22886])).

tff(c_22891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_22889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.64  
% 9.68/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.64  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 9.68/3.64  
% 9.68/3.64  %Foreground sorts:
% 9.68/3.64  
% 9.68/3.64  
% 9.68/3.64  %Background operators:
% 9.68/3.64  
% 9.68/3.64  
% 9.68/3.64  %Foreground operators:
% 9.68/3.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.68/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.68/3.64  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 9.68/3.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.68/3.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.68/3.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.68/3.64  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 9.68/3.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.68/3.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.68/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.68/3.64  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 9.68/3.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.68/3.64  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 9.68/3.64  tff('#skF_5', type, '#skF_5': $i).
% 9.68/3.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.68/3.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.68/3.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.68/3.64  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 9.68/3.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.68/3.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.68/3.64  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 9.68/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.68/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.68/3.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.68/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.68/3.64  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 9.68/3.64  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 9.68/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.68/3.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.68/3.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.68/3.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.68/3.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.68/3.64  
% 9.68/3.66  tff(f_144, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 9.68/3.66  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.68/3.66  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.68/3.66  tff(f_70, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 9.68/3.66  tff(f_86, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 9.68/3.66  tff(f_42, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.68/3.66  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.68/3.66  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 9.68/3.66  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.68/3.66  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 9.68/3.66  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.68/3.66  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.68/3.66  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.68/3.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.68/3.66  tff(f_124, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 9.68/3.66  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_72, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_155, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.68/3.66  tff(c_159, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_155])).
% 9.68/3.66  tff(c_164, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.68/3.66  tff(c_167, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_159, c_164])).
% 9.68/3.66  tff(c_172, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_167])).
% 9.68/3.66  tff(c_173, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_172])).
% 9.68/3.66  tff(c_46, plain, (![A_26]: (k9_setfam_1(A_26)=k1_zfmisc_1(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.68/3.66  tff(c_54, plain, (![A_30]: (u1_struct_0(k3_yellow_1(A_30))=k9_setfam_1(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.68/3.66  tff(c_68, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_75, plain, (v1_subset_1('#skF_5', k9_setfam_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 9.68/3.66  tff(c_80, plain, (v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75])).
% 9.68/3.66  tff(c_66, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_64, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 9.68/3.66  tff(c_81, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76])).
% 9.68/3.66  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_24, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.68/3.66  tff(c_320, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.68/3.66  tff(c_323, plain, (![C_76]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', C_76)=k4_xboole_0('#skF_5', C_76))), inference(resolution, [status(thm)], [c_81, c_320])).
% 9.68/3.66  tff(c_56, plain, (![A_31, B_33]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))), B_33, k1_tarski(k1_xboole_0))=k2_yellow19(A_31, k3_yellow19(A_31, k2_struct_0(A_31), B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))))) | ~v13_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | ~v2_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | v1_xboole_0(B_33) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.68/3.66  tff(c_78, plain, (![A_31, B_33]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_31)), B_33, k1_tarski(k1_xboole_0))=k2_yellow19(A_31, k3_yellow19(A_31, k2_struct_0(A_31), B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_31)))) | ~v13_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | ~v2_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_31))) | v1_xboole_0(B_33) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_56])).
% 9.68/3.66  tff(c_1827, plain, (![A_172, B_173]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_172)), B_173, k1_tarski(k1_xboole_0))=k2_yellow19(A_172, k3_yellow19(A_172, k2_struct_0(A_172), B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_172)))) | ~v13_waybel_0(B_173, k3_yellow_1(k2_struct_0(A_172))) | ~v2_waybel_0(B_173, k3_yellow_1(k2_struct_0(A_172))) | v1_xboole_0(B_173) | ~l1_struct_0(A_172) | v2_struct_0(A_172))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_78])).
% 9.68/3.66  tff(c_1829, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_81, c_1827])).
% 9.68/3.66  tff(c_1832, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_64, c_323, c_1829])).
% 9.68/3.66  tff(c_1833, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_1832])).
% 9.68/3.66  tff(c_60, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.68/3.66  tff(c_1872, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_60])).
% 9.68/3.66  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_906, plain, (![A_130, B_131, C_132]: (~r2_hidden('#skF_2'(A_130, B_131, C_132), C_132) | r2_hidden('#skF_3'(A_130, B_131, C_132), C_132) | k4_xboole_0(A_130, B_131)=C_132)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_919, plain, (![A_5, B_6]: (r2_hidden('#skF_3'(A_5, B_6, A_5), A_5) | k4_xboole_0(A_5, B_6)=A_5)), inference(resolution, [status(thm)], [c_22, c_906])).
% 9.68/3.66  tff(c_1269, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_2'(A_149, B_150, C_151), A_149) | r2_hidden('#skF_3'(A_149, B_150, C_151), B_150) | ~r2_hidden('#skF_3'(A_149, B_150, C_151), A_149) | k4_xboole_0(A_149, B_150)=C_151)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_12, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), A_5) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_3632, plain, (![A_257, B_258]: (r2_hidden('#skF_3'(A_257, B_258, A_257), B_258) | ~r2_hidden('#skF_3'(A_257, B_258, A_257), A_257) | k4_xboole_0(A_257, B_258)=A_257)), inference(resolution, [status(thm)], [c_1269, c_12])).
% 9.68/3.66  tff(c_3669, plain, (![A_259, B_260]: (r2_hidden('#skF_3'(A_259, B_260, A_259), B_260) | k4_xboole_0(A_259, B_260)=A_259)), inference(resolution, [status(thm)], [c_919, c_3632])).
% 9.68/3.66  tff(c_32, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.68/3.66  tff(c_139, plain, (![C_50, B_51]: (~r2_hidden(C_50, k4_xboole_0(B_51, k1_tarski(C_50))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.68/3.66  tff(c_142, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_139])).
% 9.68/3.66  tff(c_28, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.68/3.66  tff(c_180, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.68/3.66  tff(c_206, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_180])).
% 9.68/3.66  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.68/3.66  tff(c_210, plain, (![D_60, A_61, B_62]: (r2_hidden(D_60, A_61) | ~r2_hidden(D_60, k4_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_224, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(k4_xboole_0(A_61, B_62)), A_61) | v1_xboole_0(k4_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_4, c_210])).
% 9.68/3.66  tff(c_292, plain, (![D_68, B_69, A_70]: (~r2_hidden(D_68, B_69) | ~r2_hidden(D_68, k4_xboole_0(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_1428, plain, (![A_159, B_160]: (~r2_hidden('#skF_1'(k4_xboole_0(A_159, B_160)), B_160) | v1_xboole_0(k4_xboole_0(A_159, B_160)))), inference(resolution, [status(thm)], [c_4, c_292])).
% 9.68/3.66  tff(c_1446, plain, (![A_61]: (v1_xboole_0(k4_xboole_0(A_61, A_61)))), inference(resolution, [status(thm)], [c_224, c_1428])).
% 9.68/3.66  tff(c_1475, plain, (![A_161]: (v1_xboole_0(k3_xboole_0(A_161, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_1446])).
% 9.68/3.66  tff(c_696, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_2'(A_117, B_118, C_119), A_117) | r2_hidden('#skF_3'(A_117, B_118, C_119), C_119) | k4_xboole_0(A_117, B_118)=C_119)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.68/3.66  tff(c_728, plain, (![B_118, C_119]: (r2_hidden('#skF_3'(k1_xboole_0, B_118, C_119), C_119) | k4_xboole_0(k1_xboole_0, B_118)=C_119)), inference(resolution, [status(thm)], [c_696, c_142])).
% 9.68/3.66  tff(c_782, plain, (![B_120, C_121]: (r2_hidden('#skF_3'(k1_xboole_0, B_120, C_121), C_121) | k1_xboole_0=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_728])).
% 9.68/3.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.68/3.66  tff(c_824, plain, (![C_121]: (~v1_xboole_0(C_121) | k1_xboole_0=C_121)), inference(resolution, [status(thm)], [c_782, c_2])).
% 9.68/3.66  tff(c_1494, plain, (![A_161]: (k3_xboole_0(A_161, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1475, c_824])).
% 9.68/3.66  tff(c_1657, plain, (![A_167]: (k4_xboole_0(A_167, A_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_206])).
% 9.68/3.66  tff(c_38, plain, (![A_20, B_21, C_22]: (r2_hidden(A_20, k4_xboole_0(B_21, k1_tarski(C_22))) | C_22=A_20 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.68/3.66  tff(c_1688, plain, (![A_20, C_22]: (r2_hidden(A_20, k1_xboole_0) | C_22=A_20 | ~r2_hidden(A_20, k1_tarski(C_22)))), inference(superposition, [status(thm), theory('equality')], [c_1657, c_38])).
% 9.68/3.66  tff(c_1743, plain, (![C_22, A_20]: (C_22=A_20 | ~r2_hidden(A_20, k1_tarski(C_22)))), inference(negUnitSimplification, [status(thm)], [c_142, c_1688])).
% 9.68/3.66  tff(c_22209, plain, (![A_564, C_565]: ('#skF_3'(A_564, k1_tarski(C_565), A_564)=C_565 | k4_xboole_0(A_564, k1_tarski(C_565))=A_564)), inference(resolution, [status(thm)], [c_3669, c_1743])).
% 9.68/3.66  tff(c_22569, plain, ('#skF_3'('#skF_5', k1_tarski(k1_xboole_0), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22209, c_1872])).
% 9.68/3.66  tff(c_22594, plain, (r2_hidden(k1_xboole_0, '#skF_5') | k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_22569, c_919])).
% 9.68/3.66  tff(c_22609, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1872, c_22594])).
% 9.68/3.66  tff(c_58, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.68/3.66  tff(c_77, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k9_setfam_1(A_34))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, k9_setfam_1(A_34)) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_58])).
% 9.68/3.66  tff(c_82, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, k1_zfmisc_1(A_34)) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_77])).
% 9.68/3.66  tff(c_22616, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_34)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_22609, c_82])).
% 9.68/3.66  tff(c_22626, plain, (![A_34]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_34))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_34)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22616])).
% 9.68/3.66  tff(c_22883, plain, (![A_574]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_574))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_574)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_574)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_574)) | v1_xboole_0(A_574))), inference(negUnitSimplification, [status(thm)], [c_70, c_22626])).
% 9.68/3.66  tff(c_22886, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_81, c_22883])).
% 9.68/3.66  tff(c_22889, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_64, c_22886])).
% 9.68/3.66  tff(c_22891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_22889])).
% 9.68/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.68/3.66  
% 9.68/3.66  Inference rules
% 9.68/3.66  ----------------------
% 9.68/3.66  #Ref     : 0
% 9.68/3.66  #Sup     : 5933
% 9.68/3.66  #Fact    : 0
% 9.68/3.66  #Define  : 0
% 9.68/3.66  #Split   : 2
% 9.68/3.66  #Chain   : 0
% 9.68/3.66  #Close   : 0
% 9.68/3.66  
% 9.68/3.66  Ordering : KBO
% 9.68/3.66  
% 9.68/3.66  Simplification rules
% 9.68/3.66  ----------------------
% 9.68/3.66  #Subsume      : 2577
% 9.68/3.66  #Demod        : 3043
% 9.68/3.66  #Tautology    : 1873
% 9.68/3.66  #SimpNegUnit  : 134
% 9.68/3.66  #BackRed      : 11
% 9.68/3.66  
% 9.68/3.66  #Partial instantiations: 0
% 9.68/3.66  #Strategies tried      : 1
% 9.68/3.66  
% 9.68/3.66  Timing (in seconds)
% 9.68/3.66  ----------------------
% 9.68/3.66  Preprocessing        : 0.35
% 9.68/3.66  Parsing              : 0.19
% 9.68/3.66  CNF conversion       : 0.02
% 9.68/3.66  Main loop            : 2.53
% 9.68/3.66  Inferencing          : 0.70
% 9.68/3.66  Reduction            : 0.77
% 9.68/3.66  Demodulation         : 0.55
% 9.68/3.66  BG Simplification    : 0.08
% 9.68/3.66  Subsumption          : 0.84
% 9.68/3.66  Abstraction          : 0.13
% 9.68/3.66  MUC search           : 0.00
% 9.68/3.66  Cooper               : 0.00
% 9.68/3.66  Total                : 2.92
% 9.68/3.66  Index Insertion      : 0.00
% 9.68/3.66  Index Deletion       : 0.00
% 9.68/3.66  Index Matching       : 0.00
% 9.68/3.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
