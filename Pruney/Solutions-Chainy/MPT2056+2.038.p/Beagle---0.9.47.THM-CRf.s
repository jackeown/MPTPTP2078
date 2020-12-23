%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 14.46s
% Output     : CNFRefutation 14.68s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 313 expanded)
%              Number of leaves         :   52 ( 131 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 732 expanded)
%              Number of equality atoms :   56 ( 188 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_129,axiom,(
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

tff(f_72,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_150,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_74,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_113,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_117,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_113])).

tff(c_150,plain,(
    ! [A_63] :
      ( ~ v1_xboole_0(u1_struct_0(A_63))
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_153,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_150])).

tff(c_155,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_153])).

tff(c_156,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_155])).

tff(c_70,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_68,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_66,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_759,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_subset_1(A_119,B_120,C_121) = k4_xboole_0(B_120,C_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_762,plain,(
    ! [C_121] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_121) = k4_xboole_0('#skF_6',C_121) ),
    inference(resolution,[status(thm)],[c_64,c_759])).

tff(c_2230,plain,(
    ! [A_219,B_220] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_219))),B_220,k1_tarski(k1_xboole_0)) = k2_yellow19(A_219,k3_yellow19(A_219,k2_struct_0(A_219),B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_219)))))
      | ~ v13_waybel_0(B_220,k3_yellow_1(k2_struct_0(A_219)))
      | ~ v2_waybel_0(B_220,k3_yellow_1(k2_struct_0(A_219)))
      | v1_xboole_0(B_220)
      | ~ l1_struct_0(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2232,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2230])).

tff(c_2235,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_762,c_2232])).

tff(c_2236,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_72,c_2235])).

tff(c_62,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2354,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_62])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_401,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(k2_xboole_0(A_93,B_94),B_94) = A_93
      | ~ r1_xboole_0(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_417,plain,(
    ! [A_93] :
      ( k2_xboole_0(A_93,k1_xboole_0) = A_93
      | ~ r1_xboole_0(A_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_34])).

tff(c_431,plain,(
    ! [A_95] : k2_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_417])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_443,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_36])).

tff(c_167,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_167])).

tff(c_520,plain,(
    ! [A_98] : k3_xboole_0(A_98,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_189])).

tff(c_32,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_538,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = k4_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_32])).

tff(c_556,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_538])).

tff(c_347,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_3'(A_85,B_86),B_86)
      | r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(k1_tarski(A_30),k1_tarski(B_31))
      | B_31 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_138,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden(A_58,B_59)
      | ~ r1_xboole_0(k1_tarski(A_58),B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_146,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,k1_tarski(B_31))
      | B_31 = A_30 ) ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_371,plain,(
    ! [A_85,B_31] :
      ( '#skF_3'(A_85,k1_tarski(B_31)) = B_31
      | r1_xboole_0(A_85,k1_tarski(B_31)) ) ),
    inference(resolution,[status(thm)],[c_347,c_146])).

tff(c_40,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1020,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_1'(A_153,B_154,C_155),A_153)
      | r2_hidden('#skF_2'(A_153,B_154,C_155),C_155)
      | k4_xboole_0(A_153,B_154) = C_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_138])).

tff(c_1051,plain,(
    ! [B_154,C_155] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_154,C_155),C_155)
      | k4_xboole_0(k1_xboole_0,B_154) = C_155 ) ),
    inference(resolution,[status(thm)],[c_1020,c_147])).

tff(c_1092,plain,(
    ! [B_156,C_157] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_156,C_157),C_157)
      | k1_xboole_0 = C_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1051])).

tff(c_30,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1128,plain,(
    ! [A_158,B_159] :
      ( ~ r1_xboole_0(A_158,B_159)
      | k3_xboole_0(A_158,B_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1092,c_30])).

tff(c_2898,plain,(
    ! [A_242,B_243] :
      ( k3_xboole_0(A_242,k1_tarski(B_243)) = k1_xboole_0
      | '#skF_3'(A_242,k1_tarski(B_243)) = B_243 ) ),
    inference(resolution,[status(thm)],[c_371,c_1128])).

tff(c_2948,plain,(
    ! [A_242,B_243] :
      ( k4_xboole_0(A_242,k1_tarski(B_243)) = k5_xboole_0(A_242,k1_xboole_0)
      | '#skF_3'(A_242,k1_tarski(B_243)) = B_243 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2898,c_32])).

tff(c_59786,plain,(
    ! [A_1004,B_1005] :
      ( k4_xboole_0(A_1004,k1_tarski(B_1005)) = A_1004
      | '#skF_3'(A_1004,k1_tarski(B_1005)) = B_1005 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_2948])).

tff(c_60535,plain,(
    '#skF_3'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59786,c_2354])).

tff(c_26,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60558,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60535,c_26])).

tff(c_60572,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_60558])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(k2_xboole_0(A_26,B_27),B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4537,plain,(
    ! [A_288,A_289,B_290] :
      ( r2_hidden('#skF_3'(A_288,k4_xboole_0(A_289,B_290)),A_289)
      | r1_xboole_0(A_288,k4_xboole_0(A_289,B_290)) ) ),
    inference(resolution,[status(thm)],[c_347,c_6])).

tff(c_230,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_3'(A_75,B_76),A_75)
      | r1_xboole_0(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_247,plain,(
    ! [A_1,B_2,B_76] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_1,B_2),B_76),B_2)
      | r1_xboole_0(k4_xboole_0(A_1,B_2),B_76) ) ),
    inference(resolution,[status(thm)],[c_230,c_4])).

tff(c_4650,plain,(
    ! [A_291,A_292,B_293] : r1_xboole_0(k4_xboole_0(A_291,A_292),k4_xboole_0(A_292,B_293)) ),
    inference(resolution,[status(thm)],[c_4537,c_247])).

tff(c_4884,plain,(
    ! [A_297,B_298,B_299] :
      ( r1_xboole_0(A_297,k4_xboole_0(B_298,B_299))
      | ~ r1_xboole_0(A_297,B_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4650])).

tff(c_1124,plain,(
    ! [A_12,B_13] :
      ( ~ r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1092,c_30])).

tff(c_15385,plain,(
    ! [A_483,B_484,B_485] :
      ( k3_xboole_0(A_483,k4_xboole_0(B_484,B_485)) = k1_xboole_0
      | ~ r1_xboole_0(A_483,B_484) ) ),
    inference(resolution,[status(thm)],[c_4884,c_1124])).

tff(c_15605,plain,(
    ! [A_483,B_484,B_485] :
      ( k4_xboole_0(A_483,k4_xboole_0(B_484,B_485)) = k5_xboole_0(A_483,k1_xboole_0)
      | ~ r1_xboole_0(A_483,B_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15385,c_32])).

tff(c_16085,plain,(
    ! [A_492,B_493,B_494] :
      ( k4_xboole_0(A_492,k4_xboole_0(B_493,B_494)) = A_492
      | ~ r1_xboole_0(A_492,B_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_15605])).

tff(c_16445,plain,(
    ! [A_492,A_19] :
      ( k4_xboole_0(A_492,A_19) = A_492
      | ~ r1_xboole_0(A_492,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_16085])).

tff(c_60575,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60572,c_16445])).

tff(c_60595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2354,c_60575])).

tff(c_60596,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60558])).

tff(c_60,plain,(
    ! [C_47,B_45,A_41] :
      ( ~ v1_xboole_0(C_47)
      | ~ r2_hidden(C_47,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41))))
      | ~ v13_waybel_0(B_45,k3_yellow_1(A_41))
      | ~ v2_waybel_0(B_45,k3_yellow_1(A_41))
      | ~ v1_subset_1(B_45,u1_struct_0(k3_yellow_1(A_41)))
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60605,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_41))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_41))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_41)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_60596,c_60])).

tff(c_60611,plain,(
    ! [A_41] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_41))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_41))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_41)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_60605])).

tff(c_60819,plain,(
    ! [A_1008] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_1008))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_1008))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_1008))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_1008)))
      | v1_xboole_0(A_1008) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60611])).

tff(c_60822,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_60819])).

tff(c_60825,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_60822])).

tff(c_60827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_60825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.46/7.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.58/7.81  
% 14.58/7.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.58/7.82  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 14.58/7.82  
% 14.58/7.82  %Foreground sorts:
% 14.58/7.82  
% 14.58/7.82  
% 14.58/7.82  %Background operators:
% 14.58/7.82  
% 14.58/7.82  
% 14.58/7.82  %Foreground operators:
% 14.58/7.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.58/7.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.58/7.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.58/7.82  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 14.58/7.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.58/7.82  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 14.58/7.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.58/7.82  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 14.58/7.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.58/7.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.58/7.82  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 14.58/7.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.58/7.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.58/7.82  tff('#skF_5', type, '#skF_5': $i).
% 14.58/7.82  tff('#skF_6', type, '#skF_6': $i).
% 14.58/7.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.58/7.82  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.58/7.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.58/7.82  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 14.58/7.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.58/7.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.58/7.82  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 14.58/7.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.58/7.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.58/7.82  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 14.58/7.82  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 14.58/7.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.58/7.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.58/7.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.58/7.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.58/7.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.58/7.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.58/7.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.58/7.82  
% 14.68/7.83  tff(f_170, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 14.68/7.83  tff(f_102, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 14.68/7.83  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 14.68/7.83  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.68/7.83  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.68/7.83  tff(f_129, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 14.68/7.83  tff(f_72, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.68/7.83  tff(f_80, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 14.68/7.83  tff(f_84, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 14.68/7.83  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.68/7.83  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.68/7.83  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.68/7.83  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.68/7.83  tff(f_94, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 14.68/7.83  tff(f_89, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 14.68/7.83  tff(f_78, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 14.68/7.83  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.68/7.83  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.68/7.83  tff(f_150, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 14.68/7.83  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_74, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_113, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.68/7.83  tff(c_117, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_113])).
% 14.68/7.83  tff(c_150, plain, (![A_63]: (~v1_xboole_0(u1_struct_0(A_63)) | ~l1_struct_0(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.68/7.83  tff(c_153, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_117, c_150])).
% 14.68/7.83  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_153])).
% 14.68/7.83  tff(c_156, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_155])).
% 14.68/7.83  tff(c_70, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_68, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_66, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_72, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.68/7.83  tff(c_759, plain, (![A_119, B_120, C_121]: (k7_subset_1(A_119, B_120, C_121)=k4_xboole_0(B_120, C_121) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.68/7.83  tff(c_762, plain, (![C_121]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_121)=k4_xboole_0('#skF_6', C_121))), inference(resolution, [status(thm)], [c_64, c_759])).
% 14.68/7.83  tff(c_2230, plain, (![A_219, B_220]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_219))), B_220, k1_tarski(k1_xboole_0))=k2_yellow19(A_219, k3_yellow19(A_219, k2_struct_0(A_219), B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_219))))) | ~v13_waybel_0(B_220, k3_yellow_1(k2_struct_0(A_219))) | ~v2_waybel_0(B_220, k3_yellow_1(k2_struct_0(A_219))) | v1_xboole_0(B_220) | ~l1_struct_0(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.68/7.83  tff(c_2232, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_2230])).
% 14.68/7.83  tff(c_2235, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_762, c_2232])).
% 14.68/7.83  tff(c_2236, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_76, c_72, c_2235])).
% 14.68/7.83  tff(c_62, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_170])).
% 14.68/7.83  tff(c_2354, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_62])).
% 14.68/7.83  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.68/7.83  tff(c_42, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.68/7.83  tff(c_401, plain, (![A_93, B_94]: (k4_xboole_0(k2_xboole_0(A_93, B_94), B_94)=A_93 | ~r1_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.68/7.83  tff(c_417, plain, (![A_93]: (k2_xboole_0(A_93, k1_xboole_0)=A_93 | ~r1_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_401, c_34])).
% 14.68/7.83  tff(c_431, plain, (![A_95]: (k2_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_417])).
% 14.68/7.83  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.68/7.83  tff(c_443, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_431, c_36])).
% 14.68/7.83  tff(c_167, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.68/7.83  tff(c_189, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_167])).
% 14.68/7.83  tff(c_520, plain, (![A_98]: (k3_xboole_0(A_98, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_189])).
% 14.68/7.83  tff(c_32, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.68/7.83  tff(c_538, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=k4_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_520, c_32])).
% 14.68/7.83  tff(c_556, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_538])).
% 14.68/7.83  tff(c_347, plain, (![A_85, B_86]: (r2_hidden('#skF_3'(A_85, B_86), B_86) | r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.68/7.83  tff(c_48, plain, (![A_30, B_31]: (r1_xboole_0(k1_tarski(A_30), k1_tarski(B_31)) | B_31=A_30)), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.68/7.83  tff(c_138, plain, (![A_58, B_59]: (~r2_hidden(A_58, B_59) | ~r1_xboole_0(k1_tarski(A_58), B_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.68/7.83  tff(c_146, plain, (![A_30, B_31]: (~r2_hidden(A_30, k1_tarski(B_31)) | B_31=A_30)), inference(resolution, [status(thm)], [c_48, c_138])).
% 14.68/7.83  tff(c_371, plain, (![A_85, B_31]: ('#skF_3'(A_85, k1_tarski(B_31))=B_31 | r1_xboole_0(A_85, k1_tarski(B_31)))), inference(resolution, [status(thm)], [c_347, c_146])).
% 14.68/7.83  tff(c_40, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.68/7.83  tff(c_1020, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_1'(A_153, B_154, C_155), A_153) | r2_hidden('#skF_2'(A_153, B_154, C_155), C_155) | k4_xboole_0(A_153, B_154)=C_155)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.68/7.83  tff(c_147, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_138])).
% 14.68/7.83  tff(c_1051, plain, (![B_154, C_155]: (r2_hidden('#skF_2'(k1_xboole_0, B_154, C_155), C_155) | k4_xboole_0(k1_xboole_0, B_154)=C_155)), inference(resolution, [status(thm)], [c_1020, c_147])).
% 14.68/7.83  tff(c_1092, plain, (![B_156, C_157]: (r2_hidden('#skF_2'(k1_xboole_0, B_156, C_157), C_157) | k1_xboole_0=C_157)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1051])).
% 14.68/7.83  tff(c_30, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.68/7.83  tff(c_1128, plain, (![A_158, B_159]: (~r1_xboole_0(A_158, B_159) | k3_xboole_0(A_158, B_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1092, c_30])).
% 14.68/7.83  tff(c_2898, plain, (![A_242, B_243]: (k3_xboole_0(A_242, k1_tarski(B_243))=k1_xboole_0 | '#skF_3'(A_242, k1_tarski(B_243))=B_243)), inference(resolution, [status(thm)], [c_371, c_1128])).
% 14.68/7.83  tff(c_2948, plain, (![A_242, B_243]: (k4_xboole_0(A_242, k1_tarski(B_243))=k5_xboole_0(A_242, k1_xboole_0) | '#skF_3'(A_242, k1_tarski(B_243))=B_243)), inference(superposition, [status(thm), theory('equality')], [c_2898, c_32])).
% 14.68/7.83  tff(c_59786, plain, (![A_1004, B_1005]: (k4_xboole_0(A_1004, k1_tarski(B_1005))=A_1004 | '#skF_3'(A_1004, k1_tarski(B_1005))=B_1005)), inference(demodulation, [status(thm), theory('equality')], [c_556, c_2948])).
% 14.68/7.83  tff(c_60535, plain, ('#skF_3'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59786, c_2354])).
% 14.68/7.83  tff(c_26, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.68/7.83  tff(c_60558, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60535, c_26])).
% 14.68/7.83  tff(c_60572, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60558])).
% 14.68/7.83  tff(c_44, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(A_26, B_27), B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.68/7.83  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.68/7.83  tff(c_4537, plain, (![A_288, A_289, B_290]: (r2_hidden('#skF_3'(A_288, k4_xboole_0(A_289, B_290)), A_289) | r1_xboole_0(A_288, k4_xboole_0(A_289, B_290)))), inference(resolution, [status(thm)], [c_347, c_6])).
% 14.68/7.83  tff(c_230, plain, (![A_75, B_76]: (r2_hidden('#skF_3'(A_75, B_76), A_75) | r1_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.68/7.83  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.68/7.83  tff(c_247, plain, (![A_1, B_2, B_76]: (~r2_hidden('#skF_3'(k4_xboole_0(A_1, B_2), B_76), B_2) | r1_xboole_0(k4_xboole_0(A_1, B_2), B_76))), inference(resolution, [status(thm)], [c_230, c_4])).
% 14.68/7.83  tff(c_4650, plain, (![A_291, A_292, B_293]: (r1_xboole_0(k4_xboole_0(A_291, A_292), k4_xboole_0(A_292, B_293)))), inference(resolution, [status(thm)], [c_4537, c_247])).
% 14.68/7.83  tff(c_4884, plain, (![A_297, B_298, B_299]: (r1_xboole_0(A_297, k4_xboole_0(B_298, B_299)) | ~r1_xboole_0(A_297, B_298))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4650])).
% 14.68/7.83  tff(c_1124, plain, (![A_12, B_13]: (~r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1092, c_30])).
% 14.68/7.83  tff(c_15385, plain, (![A_483, B_484, B_485]: (k3_xboole_0(A_483, k4_xboole_0(B_484, B_485))=k1_xboole_0 | ~r1_xboole_0(A_483, B_484))), inference(resolution, [status(thm)], [c_4884, c_1124])).
% 14.68/7.83  tff(c_15605, plain, (![A_483, B_484, B_485]: (k4_xboole_0(A_483, k4_xboole_0(B_484, B_485))=k5_xboole_0(A_483, k1_xboole_0) | ~r1_xboole_0(A_483, B_484))), inference(superposition, [status(thm), theory('equality')], [c_15385, c_32])).
% 14.68/7.83  tff(c_16085, plain, (![A_492, B_493, B_494]: (k4_xboole_0(A_492, k4_xboole_0(B_493, B_494))=A_492 | ~r1_xboole_0(A_492, B_493))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_15605])).
% 14.68/7.83  tff(c_16445, plain, (![A_492, A_19]: (k4_xboole_0(A_492, A_19)=A_492 | ~r1_xboole_0(A_492, A_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_16085])).
% 14.68/7.83  tff(c_60575, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(resolution, [status(thm)], [c_60572, c_16445])).
% 14.68/7.83  tff(c_60595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2354, c_60575])).
% 14.68/7.83  tff(c_60596, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_60558])).
% 14.68/7.83  tff(c_60, plain, (![C_47, B_45, A_41]: (~v1_xboole_0(C_47) | ~r2_hidden(C_47, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41)))) | ~v13_waybel_0(B_45, k3_yellow_1(A_41)) | ~v2_waybel_0(B_45, k3_yellow_1(A_41)) | ~v1_subset_1(B_45, u1_struct_0(k3_yellow_1(A_41))) | v1_xboole_0(B_45) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.68/7.83  tff(c_60605, plain, (![A_41]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_41)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_41)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_41))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_60596, c_60])).
% 14.68/7.83  tff(c_60611, plain, (![A_41]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_41)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_41)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_41)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_41))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_60605])).
% 14.68/7.83  tff(c_60819, plain, (![A_1008]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_1008)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_1008)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_1008)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_1008))) | v1_xboole_0(A_1008))), inference(negUnitSimplification, [status(thm)], [c_72, c_60611])).
% 14.68/7.83  tff(c_60822, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_60819])).
% 14.68/7.83  tff(c_60825, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_60822])).
% 14.68/7.83  tff(c_60827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_60825])).
% 14.68/7.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.68/7.83  
% 14.68/7.83  Inference rules
% 14.68/7.83  ----------------------
% 14.68/7.83  #Ref     : 0
% 14.68/7.83  #Sup     : 15155
% 14.68/7.83  #Fact    : 0
% 14.68/7.83  #Define  : 0
% 14.68/7.83  #Split   : 2
% 14.68/7.83  #Chain   : 0
% 14.68/7.83  #Close   : 0
% 14.68/7.83  
% 14.68/7.83  Ordering : KBO
% 14.68/7.83  
% 14.68/7.83  Simplification rules
% 14.68/7.83  ----------------------
% 14.68/7.83  #Subsume      : 2853
% 14.68/7.83  #Demod        : 12391
% 14.68/7.83  #Tautology    : 7284
% 14.68/7.83  #SimpNegUnit  : 191
% 14.68/7.83  #BackRed      : 2
% 14.68/7.83  
% 14.68/7.83  #Partial instantiations: 0
% 14.68/7.83  #Strategies tried      : 1
% 14.68/7.83  
% 14.68/7.83  Timing (in seconds)
% 14.68/7.83  ----------------------
% 14.68/7.84  Preprocessing        : 0.35
% 14.68/7.84  Parsing              : 0.18
% 14.68/7.84  CNF conversion       : 0.03
% 14.68/7.84  Main loop            : 6.72
% 14.68/7.84  Inferencing          : 1.15
% 14.68/7.84  Reduction            : 2.80
% 14.68/7.84  Demodulation         : 2.31
% 14.68/7.84  BG Simplification    : 0.14
% 14.68/7.84  Subsumption          : 2.25
% 14.68/7.84  Abstraction          : 0.22
% 14.68/7.84  MUC search           : 0.00
% 14.68/7.84  Cooper               : 0.00
% 14.68/7.84  Total                : 7.11
% 14.68/7.84  Index Insertion      : 0.00
% 14.68/7.84  Index Deletion       : 0.00
% 14.68/7.84  Index Matching       : 0.00
% 14.68/7.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
