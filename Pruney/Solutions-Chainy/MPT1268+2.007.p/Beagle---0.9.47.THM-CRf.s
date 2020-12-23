%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 135 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  149 ( 363 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_443,plain,(
    ! [B_81,A_82] :
      ( v2_tops_1(B_81,A_82)
      | k1_tops_1(A_82,B_81) != k1_xboole_0
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_450,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_443])).

tff(c_458,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_450])).

tff(c_459,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_458])).

tff(c_289,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_294,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_289])).

tff(c_301,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_347,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_352,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_347])).

tff(c_359,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_352])).

tff(c_105,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [C_38] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_38
      | ~ v3_pre_topc(C_38,'#skF_1')
      | ~ r1_tarski(C_38,'#skF_2')
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_392,plain,(
    ! [C_79] :
      ( k1_xboole_0 = C_79
      | ~ v3_pre_topc(C_79,'#skF_1')
      | ~ r1_tarski(C_79,'#skF_2')
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52])).

tff(c_577,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ v3_pre_topc(A_88,'#skF_1')
      | ~ r1_tarski(A_88,'#skF_2')
      | ~ r1_tarski(A_88,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_392])).

tff(c_599,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ v3_pre_topc(A_89,'#skF_1')
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_132,c_577])).

tff(c_602,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_359,c_599])).

tff(c_608,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_602])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_608])).

tff(c_611,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_612,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_649,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_647,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_38])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_660,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_40])).

tff(c_1315,plain,(
    ! [A_137,B_138] :
      ( k1_tops_1(A_137,B_138) = k1_xboole_0
      | ~ v2_tops_1(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1325,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1315])).

tff(c_1337,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_612,c_1325])).

tff(c_1661,plain,(
    ! [B_153,A_154,C_155] :
      ( r1_tarski(B_153,k1_tops_1(A_154,C_155))
      | ~ r1_tarski(B_153,C_155)
      | ~ v3_pre_topc(B_153,A_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1668,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_153,'#skF_2')
      | ~ v3_pre_topc(B_153,'#skF_1')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1661])).

tff(c_1681,plain,(
    ! [B_156] :
      ( r1_tarski(B_156,k1_xboole_0)
      | ~ r1_tarski(B_156,'#skF_2')
      | ~ v3_pre_topc(B_156,'#skF_1')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1337,c_1668])).

tff(c_1688,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_660,c_1681])).

tff(c_1699,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_647,c_1688])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1723,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1699,c_4])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_694,plain,(
    ! [A_98,B_99] : k1_setfam_1(k2_tarski(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_722,plain,(
    ! [B_102,A_103] : k1_setfam_1(k2_tarski(B_102,A_103)) = k3_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_694])).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_745,plain,(
    ! [B_104,A_105] : k3_xboole_0(B_104,A_105) = k3_xboole_0(A_105,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_10])).

tff(c_8,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_661,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_674,plain,(
    ! [A_96] : r1_tarski(k1_xboole_0,A_96) ),
    inference(resolution,[status(thm)],[c_8,c_661])).

tff(c_678,plain,(
    ! [A_96] : k3_xboole_0(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_674,c_4])).

tff(c_761,plain,(
    ! [B_104] : k3_xboole_0(B_104,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_678])).

tff(c_1763,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_761])).

tff(c_1769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_1763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.55  
% 3.56/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.55  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.56/1.55  
% 3.56/1.55  %Foreground sorts:
% 3.56/1.55  
% 3.56/1.55  
% 3.56/1.55  %Background operators:
% 3.56/1.55  
% 3.56/1.55  
% 3.56/1.55  %Foreground operators:
% 3.56/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.56/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.55  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.56/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.56/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.56/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.56/1.55  
% 3.56/1.57  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.56/1.57  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.56/1.57  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.56/1.57  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.56/1.57  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.57  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.56/1.57  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.56/1.57  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.57  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.56/1.57  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.56/1.57  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.56/1.57  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_54, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.56/1.57  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_443, plain, (![B_81, A_82]: (v2_tops_1(B_81, A_82) | k1_tops_1(A_82, B_81)!=k1_xboole_0 | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.57  tff(c_450, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_443])).
% 3.56/1.57  tff(c_458, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_450])).
% 3.56/1.57  tff(c_459, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_458])).
% 3.56/1.57  tff(c_289, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.56/1.57  tff(c_294, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_289])).
% 3.56/1.57  tff(c_301, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_294])).
% 3.56/1.57  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_347, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.56/1.57  tff(c_352, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_347])).
% 3.56/1.57  tff(c_359, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_352])).
% 3.56/1.57  tff(c_105, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.57  tff(c_116, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_105])).
% 3.56/1.57  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.57  tff(c_132, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_1')) | ~r1_tarski(A_1, '#skF_2'))), inference(resolution, [status(thm)], [c_116, c_2])).
% 3.56/1.57  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.57  tff(c_52, plain, (![C_38]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_38 | ~v3_pre_topc(C_38, '#skF_1') | ~r1_tarski(C_38, '#skF_2') | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_392, plain, (![C_79]: (k1_xboole_0=C_79 | ~v3_pre_topc(C_79, '#skF_1') | ~r1_tarski(C_79, '#skF_2') | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_52])).
% 3.56/1.57  tff(c_577, plain, (![A_88]: (k1_xboole_0=A_88 | ~v3_pre_topc(A_88, '#skF_1') | ~r1_tarski(A_88, '#skF_2') | ~r1_tarski(A_88, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_392])).
% 3.56/1.57  tff(c_599, plain, (![A_89]: (k1_xboole_0=A_89 | ~v3_pre_topc(A_89, '#skF_1') | ~r1_tarski(A_89, '#skF_2'))), inference(resolution, [status(thm)], [c_132, c_577])).
% 3.56/1.57  tff(c_602, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_359, c_599])).
% 3.56/1.57  tff(c_608, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_301, c_602])).
% 3.56/1.57  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_608])).
% 3.56/1.57  tff(c_611, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.56/1.57  tff(c_612, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.56/1.57  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_649, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_36])).
% 3.56/1.57  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_647, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_38])).
% 3.56/1.57  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.56/1.57  tff(c_660, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_40])).
% 3.56/1.57  tff(c_1315, plain, (![A_137, B_138]: (k1_tops_1(A_137, B_138)=k1_xboole_0 | ~v2_tops_1(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.57  tff(c_1325, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1315])).
% 3.56/1.57  tff(c_1337, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_612, c_1325])).
% 3.56/1.57  tff(c_1661, plain, (![B_153, A_154, C_155]: (r1_tarski(B_153, k1_tops_1(A_154, C_155)) | ~r1_tarski(B_153, C_155) | ~v3_pre_topc(B_153, A_154) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.56/1.57  tff(c_1668, plain, (![B_153]: (r1_tarski(B_153, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_153, '#skF_2') | ~v3_pre_topc(B_153, '#skF_1') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1661])).
% 3.56/1.57  tff(c_1681, plain, (![B_156]: (r1_tarski(B_156, k1_xboole_0) | ~r1_tarski(B_156, '#skF_2') | ~v3_pre_topc(B_156, '#skF_1') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1337, c_1668])).
% 3.56/1.57  tff(c_1688, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_660, c_1681])).
% 3.56/1.57  tff(c_1699, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_649, c_647, c_1688])).
% 3.56/1.57  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.57  tff(c_1723, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_1699, c_4])).
% 3.56/1.57  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.57  tff(c_694, plain, (![A_98, B_99]: (k1_setfam_1(k2_tarski(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.57  tff(c_722, plain, (![B_102, A_103]: (k1_setfam_1(k2_tarski(B_102, A_103))=k3_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_6, c_694])).
% 3.56/1.57  tff(c_10, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.57  tff(c_745, plain, (![B_104, A_105]: (k3_xboole_0(B_104, A_105)=k3_xboole_0(A_105, B_104))), inference(superposition, [status(thm), theory('equality')], [c_722, c_10])).
% 3.56/1.57  tff(c_8, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.57  tff(c_661, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.57  tff(c_674, plain, (![A_96]: (r1_tarski(k1_xboole_0, A_96))), inference(resolution, [status(thm)], [c_8, c_661])).
% 3.56/1.57  tff(c_678, plain, (![A_96]: (k3_xboole_0(k1_xboole_0, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_674, c_4])).
% 3.56/1.57  tff(c_761, plain, (![B_104]: (k3_xboole_0(B_104, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_745, c_678])).
% 3.56/1.57  tff(c_1763, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1723, c_761])).
% 3.56/1.57  tff(c_1769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_1763])).
% 3.56/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.57  
% 3.56/1.57  Inference rules
% 3.56/1.57  ----------------------
% 3.56/1.57  #Ref     : 0
% 3.56/1.57  #Sup     : 402
% 3.56/1.57  #Fact    : 0
% 3.56/1.57  #Define  : 0
% 3.56/1.57  #Split   : 8
% 3.56/1.57  #Chain   : 0
% 3.56/1.57  #Close   : 0
% 3.56/1.57  
% 3.56/1.57  Ordering : KBO
% 3.56/1.57  
% 3.56/1.57  Simplification rules
% 3.56/1.57  ----------------------
% 3.56/1.57  #Subsume      : 61
% 3.56/1.57  #Demod        : 179
% 3.56/1.57  #Tautology    : 231
% 3.56/1.57  #SimpNegUnit  : 6
% 3.56/1.57  #BackRed      : 5
% 3.56/1.57  
% 3.56/1.57  #Partial instantiations: 0
% 3.56/1.57  #Strategies tried      : 1
% 3.56/1.57  
% 3.56/1.57  Timing (in seconds)
% 3.56/1.57  ----------------------
% 3.56/1.57  Preprocessing        : 0.33
% 3.56/1.57  Parsing              : 0.18
% 3.56/1.57  CNF conversion       : 0.02
% 3.56/1.57  Main loop            : 0.48
% 3.56/1.57  Inferencing          : 0.17
% 3.56/1.57  Reduction            : 0.16
% 3.56/1.57  Demodulation         : 0.11
% 3.56/1.57  BG Simplification    : 0.02
% 3.56/1.57  Subsumption          : 0.09
% 3.56/1.57  Abstraction          : 0.02
% 3.56/1.57  MUC search           : 0.00
% 3.56/1.57  Cooper               : 0.00
% 3.56/1.57  Total                : 0.84
% 3.56/1.57  Index Insertion      : 0.00
% 3.56/1.57  Index Deletion       : 0.00
% 3.56/1.57  Index Matching       : 0.00
% 3.56/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
