%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 349 expanded)
%              Number of leaves         :   50 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  190 ( 838 expanded)
%              Number of equality atoms :   41 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_128,axiom,(
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

tff(f_81,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_83,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_149,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_64,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_89,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_93,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_89])).

tff(c_103,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_106,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_103])).

tff(c_108,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_106])).

tff(c_109,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_108])).

tff(c_60,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_58,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_56,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_714,plain,(
    ! [A_139,B_140,C_141] :
      ( k7_subset_1(A_139,B_140,C_141) = k4_xboole_0(B_140,C_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_717,plain,(
    ! [C_141] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_141) = k4_xboole_0('#skF_6',C_141) ),
    inference(resolution,[status(thm)],[c_54,c_714])).

tff(c_941,plain,(
    ! [A_164,B_165] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_164))),B_165,k1_tarski(k1_xboole_0)) = k2_yellow19(A_164,k3_yellow19(A_164,k2_struct_0(A_164),B_165))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_164)))))
      | ~ v13_waybel_0(B_165,k3_yellow_1(k2_struct_0(A_164)))
      | ~ v2_waybel_0(B_165,k3_yellow_1(k2_struct_0(A_164)))
      | v1_xboole_0(B_165)
      | ~ l1_struct_0(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_943,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_941])).

tff(c_946,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_717,c_943])).

tff(c_947,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_946])).

tff(c_52,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1260,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_52])).

tff(c_32,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( ~ r1_xboole_0(A_66,B_67)
      | v1_xboole_0(k3_xboole_0(A_66,B_67)) ) ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_151,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_110,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_169,plain,(
    ! [B_72] : r1_tarski(k1_xboole_0,B_72) ),
    inference(resolution,[status(thm)],[c_151,c_115])).

tff(c_172,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_186,plain,(
    ! [B_78] :
      ( k1_xboole_0 = B_78
      | ~ r1_tarski(B_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_169,c_172])).

tff(c_204,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_170,c_186])).

tff(c_307,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = k1_xboole_0
      | ~ r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_149,c_204])).

tff(c_344,plain,(
    ! [A_98] : k3_xboole_0(A_98,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_307])).

tff(c_30,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_358,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = k4_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_30])).

tff(c_370,plain,(
    ! [A_98] : k5_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_358])).

tff(c_373,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_3'(A_99,B_100),B_100)
      | r1_xboole_0(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_123,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k1_tarski(A_59),k1_tarski(B_60))
      | B_60 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,k1_tarski(B_60))
      | B_60 = A_59 ) ),
    inference(resolution,[status(thm)],[c_123,c_36])).

tff(c_915,plain,(
    ! [A_159,B_160] :
      ( '#skF_3'(A_159,k1_tarski(B_160)) = B_160
      | r1_xboole_0(A_159,k1_tarski(B_160)) ) ),
    inference(resolution,[status(thm)],[c_373,c_127])).

tff(c_214,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = k1_xboole_0
      | ~ r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_149,c_204])).

tff(c_3063,plain,(
    ! [A_290,B_291] :
      ( k3_xboole_0(A_290,k1_tarski(B_291)) = k1_xboole_0
      | '#skF_3'(A_290,k1_tarski(B_291)) = B_291 ) ),
    inference(resolution,[status(thm)],[c_915,c_214])).

tff(c_3127,plain,(
    ! [A_290,B_291] :
      ( k4_xboole_0(A_290,k1_tarski(B_291)) = k5_xboole_0(A_290,k1_xboole_0)
      | '#skF_3'(A_290,k1_tarski(B_291)) = B_291 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_30])).

tff(c_3776,plain,(
    ! [A_316,B_317] :
      ( k4_xboole_0(A_316,k1_tarski(B_317)) = A_316
      | '#skF_3'(A_316,k1_tarski(B_317)) = B_317 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_3127])).

tff(c_3810,plain,(
    '#skF_3'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3776,c_1260])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3838,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3810,c_18])).

tff(c_3879,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3838])).

tff(c_3886,plain,(
    k3_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3879,c_214])).

tff(c_3943,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3886,c_30])).

tff(c_3990,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_3943])).

tff(c_3992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1260,c_3990])).

tff(c_3993,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3838])).

tff(c_50,plain,(
    ! [C_45,B_43,A_39] :
      ( ~ v1_xboole_0(C_45)
      | ~ r2_hidden(C_45,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39))))
      | ~ v13_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v2_waybel_0(B_43,k3_yellow_1(A_39))
      | ~ v1_subset_1(B_43,u1_struct_0(k3_yellow_1(A_39)))
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4075,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_39))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_39))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_39)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_3993,c_50])).

tff(c_4091,plain,(
    ! [A_39] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_39))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_39))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_39)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4075])).

tff(c_4187,plain,(
    ! [A_325] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_325))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_325))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_325))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_325)))
      | v1_xboole_0(A_325) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4091])).

tff(c_4190,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_4187])).

tff(c_4193,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_4190])).

tff(c_4195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_4193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.95  
% 4.92/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.95  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.92/1.95  
% 4.92/1.95  %Foreground sorts:
% 4.92/1.95  
% 4.92/1.95  
% 4.92/1.95  %Background operators:
% 4.92/1.95  
% 4.92/1.95  
% 4.92/1.95  %Foreground operators:
% 4.92/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.95  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 4.92/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.95  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.92/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.92/1.95  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.92/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.92/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.92/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.92/1.95  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.92/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.92/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.92/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.92/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.92/1.95  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.92/1.95  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 4.92/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.95  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.92/1.95  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.92/1.95  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 4.92/1.95  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.92/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.92/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.95  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.92/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.92/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.92/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.95  
% 4.92/1.97  tff(f_169, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 4.92/1.97  tff(f_101, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.92/1.97  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.92/1.97  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.92/1.97  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.92/1.97  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 4.92/1.97  tff(f_81, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.92/1.97  tff(f_83, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.92/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.92/1.97  tff(f_71, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.92/1.97  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.92/1.97  tff(f_88, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.92/1.97  tff(f_77, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.92/1.97  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.92/1.97  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.92/1.97  tff(f_93, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.92/1.97  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 4.92/1.97  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_64, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_89, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.92/1.97  tff(c_93, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_89])).
% 4.92/1.97  tff(c_103, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.92/1.97  tff(c_106, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_93, c_103])).
% 4.92/1.97  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_106])).
% 4.92/1.97  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_108])).
% 4.92/1.97  tff(c_60, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_58, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_56, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_62, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.92/1.97  tff(c_714, plain, (![A_139, B_140, C_141]: (k7_subset_1(A_139, B_140, C_141)=k4_xboole_0(B_140, C_141) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.92/1.97  tff(c_717, plain, (![C_141]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_141)=k4_xboole_0('#skF_6', C_141))), inference(resolution, [status(thm)], [c_54, c_714])).
% 4.92/1.97  tff(c_941, plain, (![A_164, B_165]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_164))), B_165, k1_tarski(k1_xboole_0))=k2_yellow19(A_164, k3_yellow19(A_164, k2_struct_0(A_164), B_165)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_164))))) | ~v13_waybel_0(B_165, k3_yellow_1(k2_struct_0(A_164))) | ~v2_waybel_0(B_165, k3_yellow_1(k2_struct_0(A_164))) | v1_xboole_0(B_165) | ~l1_struct_0(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.92/1.97  tff(c_943, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_941])).
% 4.92/1.97  tff(c_946, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_717, c_943])).
% 4.92/1.97  tff(c_947, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_946])).
% 4.92/1.97  tff(c_52, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.92/1.97  tff(c_1260, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_947, c_52])).
% 4.92/1.97  tff(c_32, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.92/1.97  tff(c_34, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.92/1.97  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.97  tff(c_144, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.92/1.97  tff(c_149, plain, (![A_66, B_67]: (~r1_xboole_0(A_66, B_67) | v1_xboole_0(k3_xboole_0(A_66, B_67)))), inference(resolution, [status(thm)], [c_4, c_144])).
% 4.92/1.97  tff(c_151, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.92/1.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.97  tff(c_170, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_151, c_2])).
% 4.92/1.97  tff(c_110, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.92/1.97  tff(c_115, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_110])).
% 4.92/1.97  tff(c_169, plain, (![B_72]: (r1_tarski(k1_xboole_0, B_72))), inference(resolution, [status(thm)], [c_151, c_115])).
% 4.92/1.97  tff(c_172, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.92/1.97  tff(c_186, plain, (![B_78]: (k1_xboole_0=B_78 | ~r1_tarski(B_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_169, c_172])).
% 4.92/1.97  tff(c_204, plain, (![A_79]: (k1_xboole_0=A_79 | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_170, c_186])).
% 4.92/1.97  tff(c_307, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=k1_xboole_0 | ~r1_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_149, c_204])).
% 4.92/1.97  tff(c_344, plain, (![A_98]: (k3_xboole_0(A_98, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_307])).
% 4.92/1.97  tff(c_30, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.92/1.97  tff(c_358, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=k4_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_344, c_30])).
% 4.92/1.97  tff(c_370, plain, (![A_98]: (k5_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_358])).
% 4.92/1.97  tff(c_373, plain, (![A_99, B_100]: (r2_hidden('#skF_3'(A_99, B_100), B_100) | r1_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.92/1.97  tff(c_123, plain, (![A_59, B_60]: (r1_xboole_0(k1_tarski(A_59), k1_tarski(B_60)) | B_60=A_59)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.92/1.97  tff(c_36, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.92/1.97  tff(c_127, plain, (![A_59, B_60]: (~r2_hidden(A_59, k1_tarski(B_60)) | B_60=A_59)), inference(resolution, [status(thm)], [c_123, c_36])).
% 4.92/1.97  tff(c_915, plain, (![A_159, B_160]: ('#skF_3'(A_159, k1_tarski(B_160))=B_160 | r1_xboole_0(A_159, k1_tarski(B_160)))), inference(resolution, [status(thm)], [c_373, c_127])).
% 4.92/1.97  tff(c_214, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=k1_xboole_0 | ~r1_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_149, c_204])).
% 4.92/1.97  tff(c_3063, plain, (![A_290, B_291]: (k3_xboole_0(A_290, k1_tarski(B_291))=k1_xboole_0 | '#skF_3'(A_290, k1_tarski(B_291))=B_291)), inference(resolution, [status(thm)], [c_915, c_214])).
% 4.92/1.97  tff(c_3127, plain, (![A_290, B_291]: (k4_xboole_0(A_290, k1_tarski(B_291))=k5_xboole_0(A_290, k1_xboole_0) | '#skF_3'(A_290, k1_tarski(B_291))=B_291)), inference(superposition, [status(thm), theory('equality')], [c_3063, c_30])).
% 4.92/1.97  tff(c_3776, plain, (![A_316, B_317]: (k4_xboole_0(A_316, k1_tarski(B_317))=A_316 | '#skF_3'(A_316, k1_tarski(B_317))=B_317)), inference(demodulation, [status(thm), theory('equality')], [c_370, c_3127])).
% 4.92/1.97  tff(c_3810, plain, ('#skF_3'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3776, c_1260])).
% 4.92/1.97  tff(c_18, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.92/1.97  tff(c_3838, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3810, c_18])).
% 4.92/1.97  tff(c_3879, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3838])).
% 4.92/1.97  tff(c_3886, plain, (k3_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_3879, c_214])).
% 4.92/1.97  tff(c_3943, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3886, c_30])).
% 4.92/1.97  tff(c_3990, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_370, c_3943])).
% 4.92/1.97  tff(c_3992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1260, c_3990])).
% 4.92/1.97  tff(c_3993, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_3838])).
% 4.92/1.97  tff(c_50, plain, (![C_45, B_43, A_39]: (~v1_xboole_0(C_45) | ~r2_hidden(C_45, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39)))) | ~v13_waybel_0(B_43, k3_yellow_1(A_39)) | ~v2_waybel_0(B_43, k3_yellow_1(A_39)) | ~v1_subset_1(B_43, u1_struct_0(k3_yellow_1(A_39))) | v1_xboole_0(B_43) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.92/1.97  tff(c_4075, plain, (![A_39]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_39)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_39)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_39))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_3993, c_50])).
% 4.92/1.97  tff(c_4091, plain, (![A_39]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_39)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_39)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_39)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_39))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4075])).
% 4.92/1.97  tff(c_4187, plain, (![A_325]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_325)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_325)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_325)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_325))) | v1_xboole_0(A_325))), inference(negUnitSimplification, [status(thm)], [c_62, c_4091])).
% 4.92/1.97  tff(c_4190, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_4187])).
% 4.92/1.97  tff(c_4193, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_4190])).
% 4.92/1.97  tff(c_4195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_4193])).
% 4.92/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.97  
% 4.92/1.97  Inference rules
% 4.92/1.97  ----------------------
% 4.92/1.97  #Ref     : 0
% 4.92/1.97  #Sup     : 996
% 4.92/1.97  #Fact    : 0
% 4.92/1.97  #Define  : 0
% 4.92/1.97  #Split   : 3
% 4.92/1.97  #Chain   : 0
% 4.92/1.97  #Close   : 0
% 4.92/1.97  
% 4.92/1.97  Ordering : KBO
% 4.92/1.97  
% 4.92/1.97  Simplification rules
% 4.92/1.97  ----------------------
% 4.92/1.97  #Subsume      : 306
% 4.92/1.97  #Demod        : 287
% 4.92/1.97  #Tautology    : 386
% 4.92/1.97  #SimpNegUnit  : 40
% 4.92/1.97  #BackRed      : 1
% 4.92/1.97  
% 4.92/1.97  #Partial instantiations: 0
% 4.92/1.97  #Strategies tried      : 1
% 4.92/1.97  
% 4.92/1.97  Timing (in seconds)
% 4.92/1.97  ----------------------
% 4.92/1.98  Preprocessing        : 0.37
% 4.92/1.98  Parsing              : 0.20
% 4.92/1.98  CNF conversion       : 0.03
% 4.92/1.98  Main loop            : 0.82
% 4.92/1.98  Inferencing          : 0.29
% 4.92/1.98  Reduction            : 0.25
% 4.92/1.98  Demodulation         : 0.16
% 4.92/1.98  BG Simplification    : 0.03
% 4.92/1.98  Subsumption          : 0.18
% 4.92/1.98  Abstraction          : 0.04
% 4.92/1.98  MUC search           : 0.00
% 4.92/1.98  Cooper               : 0.00
% 4.92/1.98  Total                : 1.23
% 4.92/1.98  Index Insertion      : 0.00
% 4.92/1.98  Index Deletion       : 0.00
% 4.92/1.98  Index Matching       : 0.00
% 4.92/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
