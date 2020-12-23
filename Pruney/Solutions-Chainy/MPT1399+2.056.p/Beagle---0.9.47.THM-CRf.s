%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 734 expanded)
%              Number of leaves         :   52 ( 262 expanded)
%              Depth                    :   14
%              Number of atoms          :  227 (2122 expanded)
%              Number of equality atoms :   38 ( 338 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_158,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ! [A_58] :
      ( v4_pre_topc(k2_struct_0(A_58),A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_10])).

tff(c_209,plain,(
    ! [B_93,A_94] :
      ( ~ r1_xboole_0(B_93,A_94)
      | ~ r1_tarski(B_93,A_94)
      | v1_xboole_0(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_212,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_209])).

tff(c_215,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_212])).

tff(c_34,plain,(
    ! [A_40] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_74,plain,(
    ! [A_40] : m1_subset_1('#skF_3',k1_zfmisc_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_46,plain,(
    ! [A_56] :
      ( l1_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_122,plain,(
    ! [A_82] :
      ( u1_struct_0(A_82) = k2_struct_0(A_82)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_127,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_131,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_72,plain,(
    ! [D_71] :
      ( v3_pre_topc(D_71,'#skF_1')
      | ~ r2_hidden(D_71,'#skF_3')
      | ~ m1_subset_1(D_71,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_138,plain,(
    ! [D_84] :
      ( v3_pre_topc(D_84,'#skF_1')
      | ~ r2_hidden(D_84,'#skF_3')
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72])).

tff(c_147,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_138])).

tff(c_149,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_66,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,'#skF_3')
      | ~ r2_hidden('#skF_2',D_71)
      | ~ v4_pre_topc(D_71,'#skF_1')
      | ~ v3_pre_topc(D_71,'#skF_1')
      | ~ m1_subset_1(D_71,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_319,plain,(
    ! [D_119] :
      ( r2_hidden(D_119,'#skF_3')
      | ~ r2_hidden('#skF_2',D_119)
      | ~ v4_pre_topc(D_119,'#skF_1')
      | ~ v3_pre_topc(D_119,'#skF_1')
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_66])).

tff(c_323,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_319])).

tff(c_330,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_323])).

tff(c_334,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_58,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_132,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_58])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_4])).

tff(c_217,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_226,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_3') = k4_xboole_0(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_217])).

tff(c_229,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_3') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_226])).

tff(c_271,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,B_112) = k3_subset_1(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,(
    ! [A_40] : k4_xboole_0(A_40,'#skF_3') = k3_subset_1(A_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_271])).

tff(c_279,plain,(
    ! [A_40] : k3_subset_1(A_40,'#skF_3') = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_274])).

tff(c_36,plain,(
    ! [C_47,A_41,B_45] :
      ( r2_hidden(C_47,k3_subset_1(A_41,B_45))
      | r2_hidden(C_47,B_45)
      | ~ m1_subset_1(C_47,A_41)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_41))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_373,plain,(
    ! [C_138,A_139,B_140] :
      ( r2_hidden(C_138,k3_subset_1(A_139,B_140))
      | r2_hidden(C_138,B_140)
      | ~ m1_subset_1(C_138,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139))
      | A_139 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36])).

tff(c_382,plain,(
    ! [C_138,A_40] :
      ( r2_hidden(C_138,A_40)
      | r2_hidden(C_138,'#skF_3')
      | ~ m1_subset_1(C_138,A_40)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_40))
      | A_40 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_373])).

tff(c_403,plain,(
    ! [C_141,A_142] :
      ( r2_hidden(C_141,A_142)
      | r2_hidden(C_141,'#skF_3')
      | ~ m1_subset_1(C_141,A_142)
      | A_142 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_382])).

tff(c_52,plain,(
    ! [A_59] :
      ( v3_pre_topc(k2_struct_0(A_59),A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    ! [A_36] : k2_subset_1(A_36) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_39] : m1_subset_1(k2_subset_1(A_39),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    ! [A_39] : m1_subset_1(A_39,k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_148,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_138])).

tff(c_240,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_327,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_319])).

tff(c_333,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_327])).

tff(c_335,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_338,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_335])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_338])).

tff(c_343,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_406,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_403,c_354])).

tff(c_432,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_406])).

tff(c_442,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_344,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_444,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_344])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_444])).

tff(c_455,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_42,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_470,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_455,c_42])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_470])).

tff(c_477,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_490,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_477])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_490])).

tff(c_495,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_507,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_536,plain,(
    ! [C_164,A_165,B_166] :
      ( r2_hidden(C_164,k3_subset_1(A_165,B_166))
      | r2_hidden(C_164,B_166)
      | ~ m1_subset_1(C_164,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165))
      | A_165 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36])).

tff(c_545,plain,(
    ! [C_164,A_40] :
      ( r2_hidden(C_164,A_40)
      | r2_hidden(C_164,'#skF_3')
      | ~ m1_subset_1(C_164,A_40)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_40))
      | A_40 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_536])).

tff(c_566,plain,(
    ! [C_167,A_168] :
      ( r2_hidden(C_167,A_168)
      | r2_hidden(C_167,'#skF_3')
      | ~ m1_subset_1(C_167,A_168)
      | A_168 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_545])).

tff(c_497,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_500,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_500])).

tff(c_505,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_517,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_569,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_566,c_517])).

tff(c_599,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_569])).

tff(c_600,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_599])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_159,plain,(
    ! [A_87] :
      ( ~ v1_xboole_0(u1_struct_0(A_87))
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_162,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_159])).

tff(c_163,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_162])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_176,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_176])).

tff(c_181,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_617,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_181])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_617])).

tff(c_625,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_647,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_625])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_647])).

tff(c_653,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_661,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_653,c_42])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_661])).

tff(c_669,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_684,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_669,c_42])).

tff(c_688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.95/1.45  
% 2.95/1.45  %Foreground sorts:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Background operators:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Foreground operators:
% 2.95/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.95/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.95/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.95/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.95/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.95/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.95/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.95/1.45  
% 3.34/1.47  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.34/1.47  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.47  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.34/1.47  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.34/1.47  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.34/1.47  tff(f_75, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.34/1.47  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.34/1.47  tff(f_106, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.34/1.47  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.47  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.34/1.47  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.47  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.34/1.47  tff(f_89, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.34/1.47  tff(f_130, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.34/1.47  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.34/1.47  tff(f_73, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.34/1.47  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.34/1.47  tff(f_118, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.34/1.47  tff(c_54, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.47  tff(c_80, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 3.34/1.47  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_50, plain, (![A_58]: (v4_pre_topc(k2_struct_0(A_58), A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.34/1.47  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.47  tff(c_78, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_10])).
% 3.34/1.47  tff(c_209, plain, (![B_93, A_94]: (~r1_xboole_0(B_93, A_94) | ~r1_tarski(B_93, A_94) | v1_xboole_0(B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.34/1.47  tff(c_212, plain, (~r1_tarski('#skF_3', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_209])).
% 3.34/1.47  tff(c_215, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_212])).
% 3.34/1.47  tff(c_34, plain, (![A_40]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.34/1.47  tff(c_74, plain, (![A_40]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34])).
% 3.34/1.47  tff(c_46, plain, (![A_56]: (l1_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.34/1.47  tff(c_122, plain, (![A_82]: (u1_struct_0(A_82)=k2_struct_0(A_82) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.34/1.47  tff(c_127, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_46, c_122])).
% 3.34/1.47  tff(c_131, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_127])).
% 3.34/1.47  tff(c_72, plain, (![D_71]: (v3_pre_topc(D_71, '#skF_1') | ~r2_hidden(D_71, '#skF_3') | ~m1_subset_1(D_71, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_138, plain, (![D_84]: (v3_pre_topc(D_84, '#skF_1') | ~r2_hidden(D_84, '#skF_3') | ~m1_subset_1(D_84, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_72])).
% 3.34/1.47  tff(c_147, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_138])).
% 3.34/1.47  tff(c_149, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_147])).
% 3.34/1.47  tff(c_66, plain, (![D_71]: (r2_hidden(D_71, '#skF_3') | ~r2_hidden('#skF_2', D_71) | ~v4_pre_topc(D_71, '#skF_1') | ~v3_pre_topc(D_71, '#skF_1') | ~m1_subset_1(D_71, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_319, plain, (![D_119]: (r2_hidden(D_119, '#skF_3') | ~r2_hidden('#skF_2', D_119) | ~v4_pre_topc(D_119, '#skF_1') | ~v3_pre_topc(D_119, '#skF_1') | ~m1_subset_1(D_119, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_66])).
% 3.34/1.47  tff(c_323, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_319])).
% 3.34/1.47  tff(c_330, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_149, c_323])).
% 3.34/1.47  tff(c_334, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_330])).
% 3.34/1.47  tff(c_58, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_132, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_58])).
% 3.34/1.47  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.47  tff(c_79, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 3.34/1.47  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.47  tff(c_81, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_4])).
% 3.34/1.47  tff(c_217, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.47  tff(c_226, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_3')=k4_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_217])).
% 3.34/1.47  tff(c_229, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_3')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_226])).
% 3.34/1.47  tff(c_271, plain, (![A_111, B_112]: (k4_xboole_0(A_111, B_112)=k3_subset_1(A_111, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.47  tff(c_274, plain, (![A_40]: (k4_xboole_0(A_40, '#skF_3')=k3_subset_1(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_271])).
% 3.34/1.47  tff(c_279, plain, (![A_40]: (k3_subset_1(A_40, '#skF_3')=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_274])).
% 3.34/1.47  tff(c_36, plain, (![C_47, A_41, B_45]: (r2_hidden(C_47, k3_subset_1(A_41, B_45)) | r2_hidden(C_47, B_45) | ~m1_subset_1(C_47, A_41) | ~m1_subset_1(B_45, k1_zfmisc_1(A_41)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.34/1.47  tff(c_373, plain, (![C_138, A_139, B_140]: (r2_hidden(C_138, k3_subset_1(A_139, B_140)) | r2_hidden(C_138, B_140) | ~m1_subset_1(C_138, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)) | A_139='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36])).
% 3.34/1.47  tff(c_382, plain, (![C_138, A_40]: (r2_hidden(C_138, A_40) | r2_hidden(C_138, '#skF_3') | ~m1_subset_1(C_138, A_40) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_40)) | A_40='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_279, c_373])).
% 3.34/1.47  tff(c_403, plain, (![C_141, A_142]: (r2_hidden(C_141, A_142) | r2_hidden(C_141, '#skF_3') | ~m1_subset_1(C_141, A_142) | A_142='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_382])).
% 3.34/1.47  tff(c_52, plain, (![A_59]: (v3_pre_topc(k2_struct_0(A_59), A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.34/1.47  tff(c_28, plain, (![A_36]: (k2_subset_1(A_36)=A_36)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.47  tff(c_32, plain, (![A_39]: (m1_subset_1(k2_subset_1(A_39), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.47  tff(c_76, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.34/1.47  tff(c_148, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_76, c_138])).
% 3.34/1.47  tff(c_240, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_148])).
% 3.34/1.47  tff(c_327, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_76, c_319])).
% 3.34/1.47  tff(c_333, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_240, c_327])).
% 3.34/1.47  tff(c_335, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_333])).
% 3.34/1.47  tff(c_338, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_335])).
% 3.34/1.47  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_338])).
% 3.34/1.47  tff(c_343, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_333])).
% 3.34/1.47  tff(c_354, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_343])).
% 3.34/1.47  tff(c_406, plain, (r2_hidden('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_403, c_354])).
% 3.34/1.47  tff(c_432, plain, (r2_hidden('#skF_2', '#skF_3') | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_406])).
% 3.34/1.47  tff(c_442, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(splitLeft, [status(thm)], [c_432])).
% 3.34/1.47  tff(c_344, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_333])).
% 3.34/1.47  tff(c_444, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_344])).
% 3.34/1.47  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_444])).
% 3.34/1.47  tff(c_455, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_432])).
% 3.34/1.47  tff(c_42, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.34/1.47  tff(c_470, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_455, c_42])).
% 3.34/1.47  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_470])).
% 3.34/1.47  tff(c_477, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_343])).
% 3.34/1.47  tff(c_490, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_477])).
% 3.34/1.47  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_490])).
% 3.34/1.47  tff(c_495, plain, (~v4_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_330])).
% 3.34/1.47  tff(c_507, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_495])).
% 3.34/1.47  tff(c_536, plain, (![C_164, A_165, B_166]: (r2_hidden(C_164, k3_subset_1(A_165, B_166)) | r2_hidden(C_164, B_166) | ~m1_subset_1(C_164, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)) | A_165='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36])).
% 3.34/1.47  tff(c_545, plain, (![C_164, A_40]: (r2_hidden(C_164, A_40) | r2_hidden(C_164, '#skF_3') | ~m1_subset_1(C_164, A_40) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_40)) | A_40='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_279, c_536])).
% 3.34/1.47  tff(c_566, plain, (![C_167, A_168]: (r2_hidden(C_167, A_168) | r2_hidden(C_167, '#skF_3') | ~m1_subset_1(C_167, A_168) | A_168='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_545])).
% 3.34/1.47  tff(c_497, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_333])).
% 3.34/1.47  tff(c_500, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_497])).
% 3.34/1.47  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_500])).
% 3.34/1.47  tff(c_505, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_333])).
% 3.34/1.47  tff(c_517, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_505])).
% 3.34/1.47  tff(c_569, plain, (r2_hidden('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_566, c_517])).
% 3.34/1.47  tff(c_599, plain, (r2_hidden('#skF_2', '#skF_3') | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_569])).
% 3.34/1.47  tff(c_600, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_507, c_599])).
% 3.34/1.47  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.34/1.47  tff(c_159, plain, (![A_87]: (~v1_xboole_0(u1_struct_0(A_87)) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.34/1.47  tff(c_162, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_131, c_159])).
% 3.34/1.47  tff(c_163, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_162])).
% 3.34/1.47  tff(c_164, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_163])).
% 3.34/1.47  tff(c_176, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_164])).
% 3.34/1.47  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_176])).
% 3.34/1.47  tff(c_181, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_163])).
% 3.34/1.47  tff(c_617, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_181])).
% 3.34/1.47  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_617])).
% 3.34/1.47  tff(c_625, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_505])).
% 3.34/1.47  tff(c_647, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_625])).
% 3.34/1.47  tff(c_651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_647])).
% 3.34/1.47  tff(c_653, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_495])).
% 3.34/1.47  tff(c_661, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_653, c_42])).
% 3.34/1.47  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_661])).
% 3.34/1.47  tff(c_669, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 3.34/1.47  tff(c_684, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_669, c_42])).
% 3.34/1.47  tff(c_688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_684])).
% 3.34/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.47  
% 3.34/1.47  Inference rules
% 3.34/1.47  ----------------------
% 3.34/1.47  #Ref     : 0
% 3.34/1.47  #Sup     : 105
% 3.34/1.47  #Fact    : 4
% 3.34/1.47  #Define  : 0
% 3.34/1.47  #Split   : 10
% 3.34/1.47  #Chain   : 0
% 3.34/1.47  #Close   : 0
% 3.34/1.47  
% 3.34/1.47  Ordering : KBO
% 3.34/1.47  
% 3.34/1.47  Simplification rules
% 3.34/1.47  ----------------------
% 3.34/1.47  #Subsume      : 7
% 3.34/1.47  #Demod        : 66
% 3.34/1.47  #Tautology    : 56
% 3.34/1.47  #SimpNegUnit  : 5
% 3.34/1.47  #BackRed      : 21
% 3.34/1.47  
% 3.34/1.47  #Partial instantiations: 0
% 3.34/1.47  #Strategies tried      : 1
% 3.34/1.47  
% 3.34/1.47  Timing (in seconds)
% 3.34/1.47  ----------------------
% 3.34/1.47  Preprocessing        : 0.36
% 3.34/1.47  Parsing              : 0.19
% 3.34/1.47  CNF conversion       : 0.03
% 3.34/1.47  Main loop            : 0.32
% 3.34/1.47  Inferencing          : 0.11
% 3.34/1.47  Reduction            : 0.10
% 3.34/1.47  Demodulation         : 0.07
% 3.34/1.47  BG Simplification    : 0.02
% 3.34/1.47  Subsumption          : 0.05
% 3.34/1.47  Abstraction          : 0.02
% 3.34/1.47  MUC search           : 0.00
% 3.34/1.47  Cooper               : 0.00
% 3.34/1.47  Total                : 0.73
% 3.34/1.47  Index Insertion      : 0.00
% 3.34/1.47  Index Deletion       : 0.00
% 3.34/1.47  Index Matching       : 0.00
% 3.34/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
