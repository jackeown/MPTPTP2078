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
% DateTime   : Thu Dec  3 10:21:38 EST 2020

% Result     : Theorem 20.69s
% Output     : CNFRefutation 21.15s
% Verified   : 
% Statistics : Number of formulae       :  640 (15497 expanded)
%              Number of leaves         :   53 (5309 expanded)
%              Depth                    :   28
%              Number of atoms          : 1872 (44819 expanded)
%              Number of equality atoms :  343 (9857 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v1_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( C != k1_xboole_0
                      & v3_pre_topc(C,A)
                      & r1_xboole_0(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k2_pre_topc(A,B)
              <=> ! [D] :
                    ( r2_hidden(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(E,A)
                              & r2_hidden(D,E)
                              & r1_xboole_0(B,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ( ~ v2_struct_0(A)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

tff(f_156,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(c_98,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_106,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_167,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_68,plain,(
    ! [A_111] :
      ( l1_struct_0(A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_168,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = k2_struct_0(A_159)
      | ~ l1_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_174,plain,(
    ! [A_162] :
      ( u1_struct_0(A_162) = k2_struct_0(A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_68,c_168])).

tff(c_178,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_174])).

tff(c_96,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_179,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_96])).

tff(c_17868,plain,(
    ! [B_1182,A_1183] :
      ( v1_tops_1(B_1182,A_1183)
      | k2_pre_topc(A_1183,B_1182) != k2_struct_0(A_1183)
      | ~ m1_subset_1(B_1182,k1_zfmisc_1(u1_struct_0(A_1183)))
      | ~ l1_pre_topc(A_1183) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_17871,plain,(
    ! [B_1182] :
      ( v1_tops_1(B_1182,'#skF_5')
      | k2_pre_topc('#skF_5',B_1182) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1182,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_17868])).

tff(c_18120,plain,(
    ! [B_1207] :
      ( v1_tops_1(B_1207,'#skF_5')
      | k2_pre_topc('#skF_5',B_1207) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1207,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_17871])).

tff(c_18123,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_18120])).

tff(c_18134,plain,(
    k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_18123])).

tff(c_18,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_17826,plain,(
    ! [A_1177,B_1178] :
      ( k2_pre_topc(A_1177,B_1178) = B_1178
      | ~ v4_pre_topc(B_1178,A_1177)
      | ~ m1_subset_1(B_1178,k1_zfmisc_1(u1_struct_0(A_1177)))
      | ~ l1_pre_topc(A_1177) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_17846,plain,(
    ! [A_1180] :
      ( k2_pre_topc(A_1180,u1_struct_0(A_1180)) = u1_struct_0(A_1180)
      | ~ v4_pre_topc(u1_struct_0(A_1180),A_1180)
      | ~ l1_pre_topc(A_1180) ) ),
    inference(resolution,[status(thm)],[c_121,c_17826])).

tff(c_17849,plain,
    ( k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) = u1_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_17846])).

tff(c_17851,plain,
    ( k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_178,c_178,c_17849])).

tff(c_17852,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17851])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_390,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,B_193) = k3_subset_1(A_192,B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_399,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k3_subset_1(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_390])).

tff(c_403,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_399])).

tff(c_314,plain,(
    ! [A_187,B_188] :
      ( k3_subset_1(A_187,k3_subset_1(A_187,B_188)) = B_188
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_323,plain,(
    ! [A_20] : k3_subset_1(A_20,k3_subset_1(A_20,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_314])).

tff(c_404,plain,(
    ! [A_20] : k3_subset_1(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_323])).

tff(c_18217,plain,(
    ! [B_1214,A_1215] :
      ( v4_pre_topc(B_1214,A_1215)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1215),B_1214),A_1215)
      | ~ m1_subset_1(B_1214,k1_zfmisc_1(u1_struct_0(A_1215)))
      | ~ l1_pre_topc(A_1215) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_18221,plain,(
    ! [A_1215] :
      ( v4_pre_topc(u1_struct_0(A_1215),A_1215)
      | ~ v3_pre_topc(k1_xboole_0,A_1215)
      | ~ m1_subset_1(u1_struct_0(A_1215),k1_zfmisc_1(u1_struct_0(A_1215)))
      | ~ l1_pre_topc(A_1215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_18217])).

tff(c_18257,plain,(
    ! [A_1218] :
      ( v4_pre_topc(u1_struct_0(A_1218),A_1218)
      | ~ v3_pre_topc(k1_xboole_0,A_1218)
      | ~ l1_pre_topc(A_1218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_18221])).

tff(c_18263,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18257])).

tff(c_18266,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_18263])).

tff(c_18267,plain,(
    ~ v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_17852,c_18266])).

tff(c_18383,plain,(
    ! [A_1231,B_1232,C_1233] :
      ( r2_hidden('#skF_2'(A_1231,B_1232,C_1233),u1_struct_0(A_1231))
      | k2_pre_topc(A_1231,B_1232) = C_1233
      | ~ m1_subset_1(C_1233,k1_zfmisc_1(u1_struct_0(A_1231)))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(u1_struct_0(A_1231)))
      | ~ l1_pre_topc(A_1231) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18394,plain,(
    ! [B_1232,C_1233] :
      ( r2_hidden('#skF_2'('#skF_5',B_1232,C_1233),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1232) = C_1233
      | ~ m1_subset_1(C_1233,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18383])).

tff(c_18399,plain,(
    ! [B_1232,C_1233] :
      ( r2_hidden('#skF_2'('#skF_5',B_1232,C_1233),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1232) = C_1233
      | ~ m1_subset_1(C_1233,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_178,c_178,c_18394])).

tff(c_18915,plain,(
    ! [B_1317,A_1318,C_1319] :
      ( r1_xboole_0(B_1317,'#skF_3'(A_1318,B_1317,C_1319))
      | ~ r2_hidden('#skF_2'(A_1318,B_1317,C_1319),C_1319)
      | k2_pre_topc(A_1318,B_1317) = C_1319
      | ~ m1_subset_1(C_1319,k1_zfmisc_1(u1_struct_0(A_1318)))
      | ~ m1_subset_1(B_1317,k1_zfmisc_1(u1_struct_0(A_1318)))
      | ~ l1_pre_topc(A_1318) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18939,plain,(
    ! [B_1232] :
      ( r1_xboole_0(B_1232,'#skF_3'('#skF_5',B_1232,k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1232) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_18399,c_18915])).

tff(c_18950,plain,(
    ! [B_1232] :
      ( r1_xboole_0(B_1232,'#skF_3'('#skF_5',B_1232,k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_1232) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_18939])).

tff(c_18818,plain,(
    ! [A_1302,B_1303,C_1304] :
      ( v3_pre_topc('#skF_3'(A_1302,B_1303,C_1304),A_1302)
      | ~ r2_hidden('#skF_2'(A_1302,B_1303,C_1304),C_1304)
      | k2_pre_topc(A_1302,B_1303) = C_1304
      | ~ m1_subset_1(C_1304,k1_zfmisc_1(u1_struct_0(A_1302)))
      | ~ m1_subset_1(B_1303,k1_zfmisc_1(u1_struct_0(A_1302)))
      | ~ l1_pre_topc(A_1302) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18839,plain,(
    ! [B_1232] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1232,k2_struct_0('#skF_5')),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1232) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_18399,c_18818])).

tff(c_18849,plain,(
    ! [B_1232] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1232,k2_struct_0('#skF_5')),'#skF_5')
      | k2_pre_topc('#skF_5',B_1232) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_18839])).

tff(c_19078,plain,(
    ! [A_1327,B_1328,C_1329] :
      ( m1_subset_1('#skF_3'(A_1327,B_1328,C_1329),k1_zfmisc_1(u1_struct_0(A_1327)))
      | ~ r2_hidden('#skF_2'(A_1327,B_1328,C_1329),C_1329)
      | k2_pre_topc(A_1327,B_1328) = C_1329
      | ~ m1_subset_1(C_1329,k1_zfmisc_1(u1_struct_0(A_1327)))
      | ~ m1_subset_1(B_1328,k1_zfmisc_1(u1_struct_0(A_1327)))
      | ~ l1_pre_topc(A_1327) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19102,plain,(
    ! [B_1232] :
      ( m1_subset_1('#skF_3'('#skF_5',B_1232,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1232) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1232,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_18399,c_19078])).

tff(c_19117,plain,(
    ! [B_1330] :
      ( m1_subset_1('#skF_3'('#skF_5',B_1330,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_1330) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1330,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_178,c_19102])).

tff(c_120,plain,(
    ! [C_151] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_474,plain,(
    ! [C_151] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_120])).

tff(c_475,plain,(
    ! [C_151] :
      ( ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_474])).

tff(c_19190,plain,(
    ! [B_1334] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_1334,k2_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_1334,k2_struct_0('#skF_5')),'#skF_5')
      | '#skF_3'('#skF_5',B_1334,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_1334) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1334,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_19117,c_475])).

tff(c_27216,plain,(
    ! [B_1715] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_1715,k2_struct_0('#skF_5')))
      | '#skF_3'('#skF_5',B_1715,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_1715) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1715,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_18849,c_19190])).

tff(c_27220,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_18950,c_27216])).

tff(c_27229,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_27220])).

tff(c_27230,plain,(
    '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18134,c_27229])).

tff(c_27266,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27230,c_18849])).

tff(c_27297,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_27266])).

tff(c_27299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18134,c_18267,c_27297])).

tff(c_27301,plain,(
    v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_17851])).

tff(c_27611,plain,(
    ! [A_1742,B_1743] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_1742),B_1743),A_1742)
      | ~ v4_pre_topc(B_1743,A_1742)
      | ~ m1_subset_1(B_1743,k1_zfmisc_1(u1_struct_0(A_1742)))
      | ~ l1_pre_topc(A_1742) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_27615,plain,(
    ! [A_1742] :
      ( v3_pre_topc(k1_xboole_0,A_1742)
      | ~ v4_pre_topc(u1_struct_0(A_1742),A_1742)
      | ~ m1_subset_1(u1_struct_0(A_1742),k1_zfmisc_1(u1_struct_0(A_1742)))
      | ~ l1_pre_topc(A_1742) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_27611])).

tff(c_27629,plain,(
    ! [A_1744] :
      ( v3_pre_topc(k1_xboole_0,A_1744)
      | ~ v4_pre_topc(u1_struct_0(A_1744),A_1744)
      | ~ l1_pre_topc(A_1744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_27615])).

tff(c_27632,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_27629])).

tff(c_27634,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_27301,c_27632])).

tff(c_27306,plain,(
    ! [B_1716,A_1717] :
      ( v1_tops_1(B_1716,A_1717)
      | k2_pre_topc(A_1717,B_1716) != k2_struct_0(A_1717)
      | ~ m1_subset_1(B_1716,k1_zfmisc_1(u1_struct_0(A_1717)))
      | ~ l1_pre_topc(A_1717) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_27309,plain,(
    ! [B_1716] :
      ( v1_tops_1(B_1716,'#skF_5')
      | k2_pre_topc('#skF_5',B_1716) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1716,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_27306])).

tff(c_27533,plain,(
    ! [B_1736] :
      ( v1_tops_1(B_1736,'#skF_5')
      | k2_pre_topc('#skF_5',B_1736) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1736,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_27309])).

tff(c_27536,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_27533])).

tff(c_27547,plain,(
    k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_27536])).

tff(c_27821,plain,(
    ! [A_1762,B_1763,C_1764] :
      ( r2_hidden('#skF_2'(A_1762,B_1763,C_1764),u1_struct_0(A_1762))
      | k2_pre_topc(A_1762,B_1763) = C_1764
      | ~ m1_subset_1(C_1764,k1_zfmisc_1(u1_struct_0(A_1762)))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(u1_struct_0(A_1762)))
      | ~ l1_pre_topc(A_1762) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_27829,plain,(
    ! [B_1763,C_1764] :
      ( r2_hidden('#skF_2'('#skF_5',B_1763,C_1764),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1763) = C_1764
      | ~ m1_subset_1(C_1764,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_27821])).

tff(c_27833,plain,(
    ! [B_1763,C_1764] :
      ( r2_hidden('#skF_2'('#skF_5',B_1763,C_1764),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1763) = C_1764
      | ~ m1_subset_1(C_1764,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_178,c_178,c_27829])).

tff(c_28309,plain,(
    ! [B_1842,A_1843,C_1844] :
      ( r1_xboole_0(B_1842,'#skF_3'(A_1843,B_1842,C_1844))
      | ~ r2_hidden('#skF_2'(A_1843,B_1842,C_1844),C_1844)
      | k2_pre_topc(A_1843,B_1842) = C_1844
      | ~ m1_subset_1(C_1844,k1_zfmisc_1(u1_struct_0(A_1843)))
      | ~ m1_subset_1(B_1842,k1_zfmisc_1(u1_struct_0(A_1843)))
      | ~ l1_pre_topc(A_1843) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28330,plain,(
    ! [B_1763] :
      ( r1_xboole_0(B_1763,'#skF_3'('#skF_5',B_1763,k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1763) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_27833,c_28309])).

tff(c_28341,plain,(
    ! [B_1763] :
      ( r1_xboole_0(B_1763,'#skF_3'('#skF_5',B_1763,k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_1763) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_28330])).

tff(c_28221,plain,(
    ! [A_1827,B_1828,C_1829] :
      ( v3_pre_topc('#skF_3'(A_1827,B_1828,C_1829),A_1827)
      | ~ r2_hidden('#skF_2'(A_1827,B_1828,C_1829),C_1829)
      | k2_pre_topc(A_1827,B_1828) = C_1829
      | ~ m1_subset_1(C_1829,k1_zfmisc_1(u1_struct_0(A_1827)))
      | ~ m1_subset_1(B_1828,k1_zfmisc_1(u1_struct_0(A_1827)))
      | ~ l1_pre_topc(A_1827) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28236,plain,(
    ! [B_1763] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1763,k2_struct_0('#skF_5')),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1763) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_27833,c_28221])).

tff(c_28245,plain,(
    ! [B_1763] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1763,k2_struct_0('#skF_5')),'#skF_5')
      | k2_pre_topc('#skF_5',B_1763) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_28236])).

tff(c_28445,plain,(
    ! [A_1856,B_1857,C_1858] :
      ( m1_subset_1('#skF_3'(A_1856,B_1857,C_1858),k1_zfmisc_1(u1_struct_0(A_1856)))
      | ~ r2_hidden('#skF_2'(A_1856,B_1857,C_1858),C_1858)
      | k2_pre_topc(A_1856,B_1857) = C_1858
      | ~ m1_subset_1(C_1858,k1_zfmisc_1(u1_struct_0(A_1856)))
      | ~ m1_subset_1(B_1857,k1_zfmisc_1(u1_struct_0(A_1856)))
      | ~ l1_pre_topc(A_1856) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28466,plain,(
    ! [B_1763] :
      ( m1_subset_1('#skF_3'('#skF_5',B_1763,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1763) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1763,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_27833,c_28445])).

tff(c_28518,plain,(
    ! [B_1865] :
      ( m1_subset_1('#skF_3'('#skF_5',B_1865,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_1865) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1865,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_98,c_178,c_121,c_178,c_178,c_28466])).

tff(c_28860,plain,(
    ! [B_1896] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_1896,k2_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_1896,k2_struct_0('#skF_5')),'#skF_5')
      | '#skF_3'('#skF_5',B_1896,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_1896) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1896,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_28518,c_475])).

tff(c_31287,plain,(
    ! [B_2047] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_2047,k2_struct_0('#skF_5')))
      | '#skF_3'('#skF_5',B_2047,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_2047) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_2047,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_28245,c_28860])).

tff(c_31291,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28341,c_31287])).

tff(c_31300,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_31291])).

tff(c_31301,plain,(
    '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_27547,c_31300])).

tff(c_38,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),'#skF_3'(A_26,B_70,C_92))
      | ~ r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_31317,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31301,c_38])).

tff(c_31336,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_179,c_178,c_121,c_178,c_31317])).

tff(c_31337,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_27547,c_31336])).

tff(c_31368,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31337])).

tff(c_31377,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_27833,c_31368])).

tff(c_31382,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_121,c_31377])).

tff(c_31384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27547,c_31382])).

tff(c_31385,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_31337])).

tff(c_302,plain,(
    ! [A_180,C_181,B_182] :
      ( m1_subset_1(A_180,C_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(C_181))
      | ~ r2_hidden(A_180,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_311,plain,(
    ! [A_180,A_20] :
      ( m1_subset_1(A_180,A_20)
      | ~ r2_hidden(A_180,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_302])).

tff(c_31552,plain,(
    ! [A_2053] : m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_2053) ),
    inference(resolution,[status(thm)],[c_31385,c_311])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31736,plain,(
    ! [A_2060] : k4_xboole_0(A_2060,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) = k3_subset_1(A_2060,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31552,c_20])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31759,plain,(
    k3_subset_1(k1_xboole_0,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31736,c_12])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k3_subset_1(A_14,k3_subset_1(A_14,B_15)) = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_31916,plain,(
    ! [A_2067] : k3_subset_1(A_2067,k3_subset_1(A_2067,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')))) = '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_31552,c_24])).

tff(c_31945,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_31759,c_31916])).

tff(c_31963,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_31945])).

tff(c_31670,plain,(
    ! [A_11] : k4_xboole_0(A_11,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) = k3_subset_1(A_11,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31552,c_20])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31804,plain,(
    ! [A_2061] : k3_subset_1(A_2061,k3_subset_1(A_2061,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')))) = '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_31552,c_24])).

tff(c_31833,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_31759,c_31804])).

tff(c_31849,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_31833])).

tff(c_31669,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')))
    | ~ v3_pre_topc('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),'#skF_5')
    | '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31552,c_475])).

tff(c_31803,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_31669])).

tff(c_31855,plain,(
    ~ v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31803])).

tff(c_31864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27634,c_31855])).

tff(c_31865,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')))
    | '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31669])).

tff(c_31867,plain,(
    ~ r1_xboole_0('#skF_6','#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_31865])).

tff(c_31878,plain,(
    k4_xboole_0('#skF_6','#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_16,c_31867])).

tff(c_31883,plain,(
    k3_subset_1('#skF_6','#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31670,c_31878])).

tff(c_31969,plain,(
    k3_subset_1('#skF_6',k1_xboole_0) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31963,c_31883])).

tff(c_31981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_31969])).

tff(c_31982,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31865])).

tff(c_31447,plain,(
    ! [A_20] : m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_20) ),
    inference(resolution,[status(thm)],[c_31385,c_311])).

tff(c_31988,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31982,c_31447])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31417,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_16)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_31385,c_26])).

tff(c_31446,plain,(
    ! [A_16] : r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_31417])).

tff(c_31989,plain,(
    ! [A_16] : r2_hidden(k1_xboole_0,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31982,c_31446])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28603,plain,(
    ! [B_1871,D_1872,C_1873,A_1874] :
      ( ~ r1_xboole_0(B_1871,D_1872)
      | ~ r2_hidden(C_1873,D_1872)
      | ~ v3_pre_topc(D_1872,A_1874)
      | ~ m1_subset_1(D_1872,k1_zfmisc_1(u1_struct_0(A_1874)))
      | ~ r2_hidden(C_1873,k2_pre_topc(A_1874,B_1871))
      | ~ m1_subset_1(C_1873,u1_struct_0(A_1874))
      | ~ m1_subset_1(B_1871,k1_zfmisc_1(u1_struct_0(A_1874)))
      | ~ l1_pre_topc(A_1874) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32389,plain,(
    ! [C_2084,B_2085,A_2086,A_2087] :
      ( ~ r2_hidden(C_2084,B_2085)
      | ~ v3_pre_topc(B_2085,A_2086)
      | ~ m1_subset_1(B_2085,k1_zfmisc_1(u1_struct_0(A_2086)))
      | ~ r2_hidden(C_2084,k2_pre_topc(A_2086,A_2087))
      | ~ m1_subset_1(C_2084,u1_struct_0(A_2086))
      | ~ m1_subset_1(A_2087,k1_zfmisc_1(u1_struct_0(A_2086)))
      | ~ l1_pre_topc(A_2086)
      | k3_xboole_0(A_2087,B_2085) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_28603])).

tff(c_32391,plain,(
    ! [A_16,A_2086,A_2087] :
      ( ~ v3_pre_topc(A_16,A_2086)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(u1_struct_0(A_2086)))
      | ~ r2_hidden(k1_xboole_0,k2_pre_topc(A_2086,A_2087))
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_2086))
      | ~ m1_subset_1(A_2087,k1_zfmisc_1(u1_struct_0(A_2086)))
      | ~ l1_pre_topc(A_2086)
      | k3_xboole_0(A_2087,A_16) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_31989,c_32389])).

tff(c_34964,plain,(
    ! [A_2160,A_2161,A_2162] :
      ( ~ v3_pre_topc(A_2160,A_2161)
      | ~ m1_subset_1(A_2160,k1_zfmisc_1(u1_struct_0(A_2161)))
      | ~ m1_subset_1(A_2162,k1_zfmisc_1(u1_struct_0(A_2161)))
      | ~ l1_pre_topc(A_2161)
      | k3_xboole_0(A_2162,A_2160) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31988,c_31989,c_32391])).

tff(c_34969,plain,(
    ! [A_2161,A_2162] :
      ( ~ v3_pre_topc(k1_xboole_0,A_2161)
      | ~ m1_subset_1(A_2162,k1_zfmisc_1(u1_struct_0(A_2161)))
      | ~ l1_pre_topc(A_2161)
      | k3_xboole_0(A_2162,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_31988,c_34964])).

tff(c_34999,plain,(
    ! [A_2163,A_2164] :
      ( ~ v3_pre_topc(k1_xboole_0,A_2163)
      | ~ m1_subset_1(A_2164,k1_zfmisc_1(u1_struct_0(A_2163)))
      | ~ l1_pre_topc(A_2163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34969])).

tff(c_35037,plain,(
    ! [A_2165] :
      ( ~ v3_pre_topc(k1_xboole_0,A_2165)
      | ~ l1_pre_topc(A_2165) ) ),
    inference(resolution,[status(thm)],[c_31988,c_34999])).

tff(c_35040,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_27634,c_35037])).

tff(c_35044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35040])).

tff(c_35045,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_35046,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_102,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_35050,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_102])).

tff(c_35096,plain,(
    ! [A_2176,B_2177] :
      ( k3_xboole_0(A_2176,B_2177) = k1_xboole_0
      | ~ r1_xboole_0(A_2176,B_2177) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35108,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35050,c_35096])).

tff(c_35051,plain,(
    ! [A_2166] :
      ( u1_struct_0(A_2166) = k2_struct_0(A_2166)
      | ~ l1_struct_0(A_2166) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_35057,plain,(
    ! [A_2169] :
      ( u1_struct_0(A_2169) = k2_struct_0(A_2169)
      | ~ l1_pre_topc(A_2169) ) ),
    inference(resolution,[status(thm)],[c_68,c_35051])).

tff(c_35061,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_35057])).

tff(c_35062,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35061,c_96])).

tff(c_35450,plain,(
    ! [A_2210,B_2211] :
      ( k2_pre_topc(A_2210,B_2211) = B_2211
      | ~ v4_pre_topc(B_2211,A_2210)
      | ~ m1_subset_1(B_2211,k1_zfmisc_1(u1_struct_0(A_2210)))
      | ~ l1_pre_topc(A_2210) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_35453,plain,(
    ! [B_2211] :
      ( k2_pre_topc('#skF_5',B_2211) = B_2211
      | ~ v4_pre_topc(B_2211,'#skF_5')
      | ~ m1_subset_1(B_2211,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35450])).

tff(c_45921,plain,(
    ! [B_3016] :
      ( k2_pre_topc('#skF_5',B_3016) = B_3016
      | ~ v4_pre_topc(B_3016,'#skF_5')
      | ~ m1_subset_1(B_3016,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35453])).

tff(c_45937,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_45921])).

tff(c_52170,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_45937])).

tff(c_108,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_35068,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_35061,c_108])).

tff(c_45936,plain,
    ( k2_pre_topc('#skF_5','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_35068,c_45921])).

tff(c_45941,plain,(
    ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_45936])).

tff(c_100,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46176,plain,(
    ! [B_3032,A_3033] :
      ( v4_pre_topc(B_3032,A_3033)
      | k2_pre_topc(A_3033,B_3032) != B_3032
      | ~ v2_pre_topc(A_3033)
      | ~ m1_subset_1(B_3032,k1_zfmisc_1(u1_struct_0(A_3033)))
      | ~ l1_pre_topc(A_3033) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46179,plain,(
    ! [B_3032] :
      ( v4_pre_topc(B_3032,'#skF_5')
      | k2_pre_topc('#skF_5',B_3032) != B_3032
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_3032,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_46176])).

tff(c_46198,plain,(
    ! [B_3035] :
      ( v4_pre_topc(B_3035,'#skF_5')
      | k2_pre_topc('#skF_5',B_3035) != B_3035
      | ~ m1_subset_1(B_3035,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_100,c_46179])).

tff(c_46201,plain,
    ( v4_pre_topc('#skF_7','#skF_5')
    | k2_pre_topc('#skF_5','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_35068,c_46198])).

tff(c_46215,plain,(
    k2_pre_topc('#skF_5','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_45941,c_46201])).

tff(c_51854,plain,(
    ! [A_3399,B_3400,C_3401] :
      ( r2_hidden('#skF_2'(A_3399,B_3400,C_3401),u1_struct_0(A_3399))
      | k2_pre_topc(A_3399,B_3400) = C_3401
      | ~ m1_subset_1(C_3401,k1_zfmisc_1(u1_struct_0(A_3399)))
      | ~ m1_subset_1(B_3400,k1_zfmisc_1(u1_struct_0(A_3399)))
      | ~ l1_pre_topc(A_3399) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_51862,plain,(
    ! [B_3400,C_3401] :
      ( r2_hidden('#skF_2'('#skF_5',B_3400,C_3401),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3400) = C_3401
      | ~ m1_subset_1(C_3401,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3400,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_51854])).

tff(c_51905,plain,(
    ! [B_3405,C_3406] :
      ( r2_hidden('#skF_2'('#skF_5',B_3405,C_3406),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3405) = C_3406
      | ~ m1_subset_1(C_3406,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3405,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_51862])).

tff(c_35364,plain,(
    ! [A_2199,C_2200,B_2201] :
      ( m1_subset_1(A_2199,C_2200)
      | ~ m1_subset_1(B_2201,k1_zfmisc_1(C_2200))
      | ~ r2_hidden(A_2199,B_2201) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35375,plain,(
    ! [A_2199,A_13] :
      ( m1_subset_1(A_2199,A_13)
      | ~ r2_hidden(A_2199,A_13) ) ),
    inference(resolution,[status(thm)],[c_121,c_35364])).

tff(c_51915,plain,(
    ! [B_3405,C_3406] :
      ( m1_subset_1('#skF_2'('#skF_5',B_3405,C_3406),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3405) = C_3406
      | ~ m1_subset_1(C_3406,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3405,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_51905,c_35375])).

tff(c_90,plain,(
    ! [A_140] :
      ( v3_pre_topc(k2_struct_0(A_140),A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_45940,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_45921])).

tff(c_45942,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_45940])).

tff(c_35276,plain,(
    ! [A_2194,B_2195] :
      ( k4_xboole_0(A_2194,B_2195) = k3_subset_1(A_2194,B_2195)
      | ~ m1_subset_1(B_2195,k1_zfmisc_1(A_2194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35288,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k3_subset_1(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_35276])).

tff(c_35293,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35288])).

tff(c_46083,plain,(
    ! [B_3026,A_3027] :
      ( v4_pre_topc(B_3026,A_3027)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_3027),B_3026),A_3027)
      | ~ m1_subset_1(B_3026,k1_zfmisc_1(u1_struct_0(A_3027)))
      | ~ l1_pre_topc(A_3027) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46094,plain,(
    ! [A_3027] :
      ( v4_pre_topc(k1_xboole_0,A_3027)
      | ~ v3_pre_topc(u1_struct_0(A_3027),A_3027)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_3027)))
      | ~ l1_pre_topc(A_3027) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_46083])).

tff(c_46145,plain,(
    ! [A_3031] :
      ( v4_pre_topc(k1_xboole_0,A_3031)
      | ~ v3_pre_topc(u1_struct_0(A_3031),A_3031)
      | ~ l1_pre_topc(A_3031) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_46094])).

tff(c_46151,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_46145])).

tff(c_46154,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_46151])).

tff(c_46155,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_45942,c_46154])).

tff(c_46158,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_46155])).

tff(c_46162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_46158])).

tff(c_46163,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45940])).

tff(c_46164,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_45940])).

tff(c_46310,plain,(
    ! [A_3042,B_3043] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_3042),B_3043),A_3042)
      | ~ v4_pre_topc(B_3043,A_3042)
      | ~ m1_subset_1(B_3043,k1_zfmisc_1(u1_struct_0(A_3042)))
      | ~ l1_pre_topc(A_3042) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46321,plain,(
    ! [A_3042] :
      ( v3_pre_topc(u1_struct_0(A_3042),A_3042)
      | ~ v4_pre_topc(k1_xboole_0,A_3042)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_3042)))
      | ~ l1_pre_topc(A_3042) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_46310])).

tff(c_46342,plain,(
    ! [A_3045] :
      ( v3_pre_topc(u1_struct_0(A_3045),A_3045)
      | ~ v4_pre_topc(k1_xboole_0,A_3045)
      | ~ l1_pre_topc(A_3045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_46321])).

tff(c_46348,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_46342])).

tff(c_46351,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_46164,c_46348])).

tff(c_46474,plain,(
    ! [A_3056,B_3057,C_3058] :
      ( r2_hidden('#skF_2'(A_3056,B_3057,C_3058),u1_struct_0(A_3056))
      | k2_pre_topc(A_3056,B_3057) = C_3058
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(u1_struct_0(A_3056)))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(u1_struct_0(A_3056)))
      | ~ l1_pre_topc(A_3056) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46485,plain,(
    ! [B_3057,C_3058] :
      ( r2_hidden('#skF_2'('#skF_5',B_3057,C_3058),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3057) = C_3058
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_46474])).

tff(c_46490,plain,(
    ! [B_3057,C_3058] :
      ( r2_hidden('#skF_2'('#skF_5',B_3057,C_3058),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3057) = C_3058
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_46485])).

tff(c_49114,plain,(
    ! [A_3279,B_3280,C_3281,E_3282] :
      ( v3_pre_topc('#skF_3'(A_3279,B_3280,C_3281),A_3279)
      | ~ r1_xboole_0(B_3280,E_3282)
      | ~ r2_hidden('#skF_2'(A_3279,B_3280,C_3281),E_3282)
      | ~ v3_pre_topc(E_3282,A_3279)
      | ~ m1_subset_1(E_3282,k1_zfmisc_1(u1_struct_0(A_3279)))
      | k2_pre_topc(A_3279,B_3280) = C_3281
      | ~ m1_subset_1(C_3281,k1_zfmisc_1(u1_struct_0(A_3279)))
      | ~ m1_subset_1(B_3280,k1_zfmisc_1(u1_struct_0(A_3279)))
      | ~ l1_pre_topc(A_3279) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_49160,plain,(
    ! [B_3057,C_3058] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3057,C_3058),'#skF_5')
      | ~ r1_xboole_0(B_3057,k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_3057) = C_3058
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_46490,c_49114])).

tff(c_50479,plain,(
    ! [B_3357,C_3358] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3357,C_3358),'#skF_5')
      | ~ r1_xboole_0(B_3357,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3357) = C_3358
      | ~ m1_subset_1(C_3358,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3357,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_121,c_35061,c_46351,c_49160])).

tff(c_50512,plain,(
    ! [B_3359] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3359,'#skF_7'),'#skF_5')
      | ~ r1_xboole_0(B_3359,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3359) = '#skF_7'
      | ~ m1_subset_1(B_3359,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_50479])).

tff(c_50546,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_50512])).

tff(c_50560,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46163,c_50546])).

tff(c_50561,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_50560])).

tff(c_50562,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_50561])).

tff(c_50565,plain,(
    k4_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_50562])).

tff(c_50572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50565])).

tff(c_50574,plain,(
    r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50561])).

tff(c_35373,plain,(
    ! [A_2199] :
      ( m1_subset_1(A_2199,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_2199,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_35068,c_35364])).

tff(c_46424,plain,(
    ! [A_3050,C_3051,B_3052] :
      ( ~ v2_struct_0(A_3050)
      | ~ r2_hidden(C_3051,k2_pre_topc(A_3050,B_3052))
      | ~ m1_subset_1(C_3051,u1_struct_0(A_3050))
      | ~ m1_subset_1(B_3052,k1_zfmisc_1(u1_struct_0(A_3050)))
      | ~ l1_pre_topc(A_3050) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46430,plain,(
    ! [C_3051] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3051,k1_xboole_0)
      | ~ m1_subset_1(C_3051,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46163,c_46424])).

tff(c_46438,plain,(
    ! [C_3051] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3051,k1_xboole_0)
      | ~ m1_subset_1(C_3051,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_35061,c_35061,c_46430])).

tff(c_46441,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46438])).

tff(c_35484,plain,(
    ! [A_2213,B_2214] :
      ( k2_pre_topc(A_2213,B_2214) = k2_struct_0(A_2213)
      | ~ v1_tops_1(B_2214,A_2213)
      | ~ m1_subset_1(B_2214,k1_zfmisc_1(u1_struct_0(A_2213)))
      | ~ l1_pre_topc(A_2213) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_35487,plain,(
    ! [B_2214] :
      ( k2_pre_topc('#skF_5',B_2214) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_2214,'#skF_5')
      | ~ m1_subset_1(B_2214,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35484])).

tff(c_46225,plain,(
    ! [B_3036] :
      ( k2_pre_topc('#skF_5',B_3036) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_3036,'#skF_5')
      | ~ m1_subset_1(B_3036,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_46231,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_46225])).

tff(c_46243,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_46231])).

tff(c_80,plain,(
    ! [A_115,B_127,C_133] :
      ( m1_subset_1('#skF_4'(A_115,B_127,C_133),k1_zfmisc_1(u1_struct_0(A_115)))
      | r2_hidden(C_133,k2_pre_topc(A_115,B_127))
      | v2_struct_0(A_115)
      | ~ m1_subset_1(C_133,u1_struct_0(A_115))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46540,plain,(
    ! [C_3074,A_3075,B_3076] :
      ( r2_hidden(C_3074,'#skF_4'(A_3075,B_3076,C_3074))
      | r2_hidden(C_3074,k2_pre_topc(A_3075,B_3076))
      | v2_struct_0(A_3075)
      | ~ m1_subset_1(C_3074,u1_struct_0(A_3075))
      | ~ m1_subset_1(B_3076,k1_zfmisc_1(u1_struct_0(A_3075)))
      | ~ l1_pre_topc(A_3075) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46542,plain,(
    ! [C_3074,B_3076] :
      ( r2_hidden(C_3074,'#skF_4'('#skF_5',B_3076,C_3074))
      | r2_hidden(C_3074,k2_pre_topc('#skF_5',B_3076))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3074,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3076,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_46540])).

tff(c_46550,plain,(
    ! [C_3074,B_3076] :
      ( r2_hidden(C_3074,'#skF_4'('#skF_5',B_3076,C_3074))
      | r2_hidden(C_3074,k2_pre_topc('#skF_5',B_3076))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3074,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3076,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_46542])).

tff(c_46557,plain,(
    ! [C_3080,B_3081] :
      ( r2_hidden(C_3080,'#skF_4'('#skF_5',B_3081,C_3080))
      | r2_hidden(C_3080,k2_pre_topc('#skF_5',B_3081))
      | ~ m1_subset_1(C_3080,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3081,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46441,c_46550])).

tff(c_46561,plain,(
    ! [C_3080] :
      ( r2_hidden(C_3080,'#skF_4'('#skF_5','#skF_6',C_3080))
      | r2_hidden(C_3080,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_3080,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_35062,c_46557])).

tff(c_46595,plain,(
    ! [C_3086] :
      ( r2_hidden(C_3086,'#skF_4'('#skF_5','#skF_6',C_3086))
      | r2_hidden(C_3086,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3086,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46243,c_46561])).

tff(c_46752,plain,(
    ! [C_3105,A_3106] :
      ( r2_hidden(C_3105,A_3106)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_3105),k1_zfmisc_1(A_3106))
      | r2_hidden(C_3105,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3105,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_46595,c_26])).

tff(c_46756,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_46752])).

tff(c_46763,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_46243,c_35061,c_46756])).

tff(c_46764,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46441,c_46763])).

tff(c_104,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_35048,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_104])).

tff(c_47243,plain,(
    ! [B_3158,D_3159,C_3160,A_3161] :
      ( ~ r1_xboole_0(B_3158,D_3159)
      | ~ r2_hidden(C_3160,D_3159)
      | ~ v3_pre_topc(D_3159,A_3161)
      | ~ m1_subset_1(D_3159,k1_zfmisc_1(u1_struct_0(A_3161)))
      | ~ r2_hidden(C_3160,k2_pre_topc(A_3161,B_3158))
      | ~ m1_subset_1(C_3160,u1_struct_0(A_3161))
      | ~ m1_subset_1(B_3158,k1_zfmisc_1(u1_struct_0(A_3161)))
      | ~ l1_pre_topc(A_3161) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_47327,plain,(
    ! [C_3166,A_3167] :
      ( ~ r2_hidden(C_3166,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_3167)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3167)))
      | ~ r2_hidden(C_3166,k2_pre_topc(A_3167,'#skF_6'))
      | ~ m1_subset_1(C_3166,u1_struct_0(A_3167))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_3167)))
      | ~ l1_pre_topc(A_3167) ) ),
    inference(resolution,[status(thm)],[c_35050,c_47243])).

tff(c_47329,plain,(
    ! [C_3166] :
      ( ~ r2_hidden(C_3166,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_3166,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_3166,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_47327])).

tff(c_47332,plain,(
    ! [C_3168] :
      ( ~ r2_hidden(C_3168,'#skF_7')
      | ~ r2_hidden(C_3168,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3168,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_46243,c_35068,c_35048,c_47329])).

tff(c_47341,plain,(
    ! [C_3169] :
      ( ~ r2_hidden(C_3169,'#skF_7')
      | ~ m1_subset_1(C_3169,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_46764,c_47332])).

tff(c_47352,plain,(
    ! [A_2199] : ~ r2_hidden(A_2199,'#skF_7') ),
    inference(resolution,[status(thm)],[c_35373,c_47341])).

tff(c_48924,plain,(
    ! [A_3271,B_3272,C_3273,E_3274] :
      ( r2_hidden('#skF_2'(A_3271,B_3272,C_3273),C_3273)
      | ~ r1_xboole_0(B_3272,E_3274)
      | ~ r2_hidden('#skF_2'(A_3271,B_3272,C_3273),E_3274)
      | ~ v3_pre_topc(E_3274,A_3271)
      | ~ m1_subset_1(E_3274,k1_zfmisc_1(u1_struct_0(A_3271)))
      | k2_pre_topc(A_3271,B_3272) = C_3273
      | ~ m1_subset_1(C_3273,k1_zfmisc_1(u1_struct_0(A_3271)))
      | ~ m1_subset_1(B_3272,k1_zfmisc_1(u1_struct_0(A_3271)))
      | ~ l1_pre_topc(A_3271) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48970,plain,(
    ! [B_3057,C_3058] :
      ( r2_hidden('#skF_2'('#skF_5',B_3057,C_3058),C_3058)
      | ~ r1_xboole_0(B_3057,k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_3057) = C_3058
      | ~ m1_subset_1(C_3058,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3057,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_46490,c_48924])).

tff(c_51189,plain,(
    ! [B_3384,C_3385] :
      ( r2_hidden('#skF_2'('#skF_5',B_3384,C_3385),C_3385)
      | ~ r1_xboole_0(B_3384,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3384) = C_3385
      | ~ m1_subset_1(C_3385,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3384,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_121,c_35061,c_46351,c_48970])).

tff(c_51204,plain,(
    ! [B_3384] :
      ( r2_hidden('#skF_2'('#skF_5',B_3384,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_3384,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3384) = '#skF_7'
      | ~ m1_subset_1(B_3384,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_51189])).

tff(c_51778,plain,(
    ! [B_3394] :
      ( ~ r1_xboole_0(B_3394,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3394) = '#skF_7'
      | ~ m1_subset_1(B_3394,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_47352,c_51204])).

tff(c_51819,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_51778])).

tff(c_51835,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46163,c_50574,c_51819])).

tff(c_51837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_51835])).

tff(c_51839,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46438])).

tff(c_35550,plain,(
    ! [B_2222] :
      ( k2_pre_topc('#skF_5',B_2222) = B_2222
      | ~ v4_pre_topc(B_2222,'#skF_5')
      | ~ m1_subset_1(B_2222,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35453])).

tff(c_35565,plain,
    ( k2_pre_topc('#skF_5','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_35068,c_35550])).

tff(c_35569,plain,(
    ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35565])).

tff(c_35571,plain,(
    ! [B_2223,A_2224] :
      ( v4_pre_topc(B_2223,A_2224)
      | k2_pre_topc(A_2224,B_2223) != B_2223
      | ~ v2_pre_topc(A_2224)
      | ~ m1_subset_1(B_2223,k1_zfmisc_1(u1_struct_0(A_2224)))
      | ~ l1_pre_topc(A_2224) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_35574,plain,(
    ! [B_2223] :
      ( v4_pre_topc(B_2223,'#skF_5')
      | k2_pre_topc('#skF_5',B_2223) != B_2223
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_2223,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35571])).

tff(c_35825,plain,(
    ! [B_2241] :
      ( v4_pre_topc(B_2241,'#skF_5')
      | k2_pre_topc('#skF_5',B_2241) != B_2241
      | ~ m1_subset_1(B_2241,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_100,c_35574])).

tff(c_35828,plain,
    ( v4_pre_topc('#skF_7','#skF_5')
    | k2_pre_topc('#skF_5','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_35068,c_35825])).

tff(c_35842,plain,(
    k2_pre_topc('#skF_5','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_35569,c_35828])).

tff(c_40625,plain,(
    ! [A_2588,B_2589,C_2590] :
      ( r2_hidden('#skF_2'(A_2588,B_2589,C_2590),u1_struct_0(A_2588))
      | k2_pre_topc(A_2588,B_2589) = C_2590
      | ~ m1_subset_1(C_2590,k1_zfmisc_1(u1_struct_0(A_2588)))
      | ~ m1_subset_1(B_2589,k1_zfmisc_1(u1_struct_0(A_2588)))
      | ~ l1_pre_topc(A_2588) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40633,plain,(
    ! [B_2589,C_2590] :
      ( r2_hidden('#skF_2'('#skF_5',B_2589,C_2590),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2589) = C_2590
      | ~ m1_subset_1(C_2590,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2589,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_40625])).

tff(c_40740,plain,(
    ! [B_2602,C_2603] :
      ( r2_hidden('#skF_2'('#skF_5',B_2602,C_2603),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2602) = C_2603
      | ~ m1_subset_1(C_2603,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2602,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_40633])).

tff(c_40750,plain,(
    ! [B_2602,C_2603] :
      ( m1_subset_1('#skF_2'('#skF_5',B_2602,C_2603),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2602) = C_2603
      | ~ m1_subset_1(C_2603,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2602,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_40740,c_35375])).

tff(c_35568,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_35550])).

tff(c_35587,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35568])).

tff(c_35646,plain,(
    ! [B_2228,A_2229] :
      ( v4_pre_topc(B_2228,A_2229)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_2229),B_2228),A_2229)
      | ~ m1_subset_1(B_2228,k1_zfmisc_1(u1_struct_0(A_2229)))
      | ~ l1_pre_topc(A_2229) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_35654,plain,(
    ! [A_2229] :
      ( v4_pre_topc(k1_xboole_0,A_2229)
      | ~ v3_pre_topc(u1_struct_0(A_2229),A_2229)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_2229)))
      | ~ l1_pre_topc(A_2229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_35646])).

tff(c_35735,plain,(
    ! [A_2234] :
      ( v4_pre_topc(k1_xboole_0,A_2234)
      | ~ v3_pre_topc(u1_struct_0(A_2234),A_2234)
      | ~ l1_pre_topc(A_2234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_35654])).

tff(c_35738,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35735])).

tff(c_35740,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35738])).

tff(c_35741,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_35587,c_35740])).

tff(c_35767,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_35741])).

tff(c_35771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_35767])).

tff(c_35772,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_35568])).

tff(c_35959,plain,(
    ! [A_2248,C_2249,B_2250] :
      ( ~ v2_struct_0(A_2248)
      | ~ r2_hidden(C_2249,k2_pre_topc(A_2248,B_2250))
      | ~ m1_subset_1(C_2249,u1_struct_0(A_2248))
      | ~ m1_subset_1(B_2250,k1_zfmisc_1(u1_struct_0(A_2248)))
      | ~ l1_pre_topc(A_2248) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_35965,plain,(
    ! [C_2249] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2249,k1_xboole_0)
      | ~ m1_subset_1(C_2249,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35772,c_35959])).

tff(c_35971,plain,(
    ! [C_2249] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2249,k1_xboole_0)
      | ~ m1_subset_1(C_2249,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_35061,c_35061,c_35965])).

tff(c_35983,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35971])).

tff(c_35912,plain,(
    ! [B_2246] :
      ( k2_pre_topc('#skF_5',B_2246) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_2246,'#skF_5')
      | ~ m1_subset_1(B_2246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_35918,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_35912])).

tff(c_35932,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_35918])).

tff(c_36268,plain,(
    ! [C_2299,A_2300,B_2301] :
      ( r2_hidden(C_2299,'#skF_4'(A_2300,B_2301,C_2299))
      | r2_hidden(C_2299,k2_pre_topc(A_2300,B_2301))
      | v2_struct_0(A_2300)
      | ~ m1_subset_1(C_2299,u1_struct_0(A_2300))
      | ~ m1_subset_1(B_2301,k1_zfmisc_1(u1_struct_0(A_2300)))
      | ~ l1_pre_topc(A_2300) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36270,plain,(
    ! [C_2299,B_2301] :
      ( r2_hidden(C_2299,'#skF_4'('#skF_5',B_2301,C_2299))
      | r2_hidden(C_2299,k2_pre_topc('#skF_5',B_2301))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_2299,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2301,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_36268])).

tff(c_36278,plain,(
    ! [C_2299,B_2301] :
      ( r2_hidden(C_2299,'#skF_4'('#skF_5',B_2301,C_2299))
      | r2_hidden(C_2299,k2_pre_topc('#skF_5',B_2301))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_2299,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2301,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_36270])).

tff(c_36317,plain,(
    ! [C_2306,B_2307] :
      ( r2_hidden(C_2306,'#skF_4'('#skF_5',B_2307,C_2306))
      | r2_hidden(C_2306,k2_pre_topc('#skF_5',B_2307))
      | ~ m1_subset_1(C_2306,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2307,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35983,c_36278])).

tff(c_36321,plain,(
    ! [C_2306] :
      ( r2_hidden(C_2306,'#skF_4'('#skF_5','#skF_6',C_2306))
      | r2_hidden(C_2306,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_2306,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_35062,c_36317])).

tff(c_36346,plain,(
    ! [C_2311] :
      ( r2_hidden(C_2311,'#skF_4'('#skF_5','#skF_6',C_2311))
      | r2_hidden(C_2311,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2311,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35932,c_36321])).

tff(c_36814,plain,(
    ! [C_2355,A_2356] :
      ( r2_hidden(C_2355,A_2356)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_2355),k1_zfmisc_1(A_2356))
      | r2_hidden(C_2355,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2355,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36346,c_26])).

tff(c_36818,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_36814])).

tff(c_36825,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_35932,c_35061,c_36818])).

tff(c_36826,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35983,c_36825])).

tff(c_36757,plain,(
    ! [B_2350,D_2351,C_2352,A_2353] :
      ( ~ r1_xboole_0(B_2350,D_2351)
      | ~ r2_hidden(C_2352,D_2351)
      | ~ v3_pre_topc(D_2351,A_2353)
      | ~ m1_subset_1(D_2351,k1_zfmisc_1(u1_struct_0(A_2353)))
      | ~ r2_hidden(C_2352,k2_pre_topc(A_2353,B_2350))
      | ~ m1_subset_1(C_2352,u1_struct_0(A_2353))
      | ~ m1_subset_1(B_2350,k1_zfmisc_1(u1_struct_0(A_2353)))
      | ~ l1_pre_topc(A_2353) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36844,plain,(
    ! [C_2358,A_2359] :
      ( ~ r2_hidden(C_2358,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_2359)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_2359)))
      | ~ r2_hidden(C_2358,k2_pre_topc(A_2359,'#skF_6'))
      | ~ m1_subset_1(C_2358,u1_struct_0(A_2359))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2359)))
      | ~ l1_pre_topc(A_2359) ) ),
    inference(resolution,[status(thm)],[c_35050,c_36757])).

tff(c_36846,plain,(
    ! [C_2358] :
      ( ~ r2_hidden(C_2358,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_2358,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_2358,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_36844])).

tff(c_36849,plain,(
    ! [C_2360] :
      ( ~ r2_hidden(C_2360,'#skF_7')
      | ~ r2_hidden(C_2360,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2360,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_35932,c_35068,c_35048,c_36846])).

tff(c_36858,plain,(
    ! [C_2361] :
      ( ~ r2_hidden(C_2361,'#skF_7')
      | ~ m1_subset_1(C_2361,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36826,c_36849])).

tff(c_36869,plain,(
    ! [A_2199] : ~ r2_hidden(A_2199,'#skF_7') ),
    inference(resolution,[status(thm)],[c_35373,c_36858])).

tff(c_35773,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_35568])).

tff(c_35889,plain,(
    ! [A_2244,B_2245] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_2244),B_2245),A_2244)
      | ~ v4_pre_topc(B_2245,A_2244)
      | ~ m1_subset_1(B_2245,k1_zfmisc_1(u1_struct_0(A_2244)))
      | ~ l1_pre_topc(A_2244) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_35900,plain,(
    ! [A_2244] :
      ( v3_pre_topc(u1_struct_0(A_2244),A_2244)
      | ~ v4_pre_topc(k1_xboole_0,A_2244)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_2244)))
      | ~ l1_pre_topc(A_2244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_35889])).

tff(c_35949,plain,(
    ! [A_2247] :
      ( v3_pre_topc(u1_struct_0(A_2247),A_2247)
      | ~ v4_pre_topc(k1_xboole_0,A_2247)
      | ~ l1_pre_topc(A_2247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_35900])).

tff(c_35955,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35949])).

tff(c_35958,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35773,c_35955])).

tff(c_34,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),u1_struct_0(A_26))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38674,plain,(
    ! [A_2486,B_2487,C_2488,E_2489] :
      ( r2_hidden('#skF_2'(A_2486,B_2487,C_2488),C_2488)
      | ~ r1_xboole_0(B_2487,E_2489)
      | ~ r2_hidden('#skF_2'(A_2486,B_2487,C_2488),E_2489)
      | ~ v3_pre_topc(E_2489,A_2486)
      | ~ m1_subset_1(E_2489,k1_zfmisc_1(u1_struct_0(A_2486)))
      | k2_pre_topc(A_2486,B_2487) = C_2488
      | ~ m1_subset_1(C_2488,k1_zfmisc_1(u1_struct_0(A_2486)))
      | ~ m1_subset_1(B_2487,k1_zfmisc_1(u1_struct_0(A_2486)))
      | ~ l1_pre_topc(A_2486) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38730,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_38674])).

tff(c_40223,plain,(
    ! [A_2576,B_2577,C_2578] :
      ( r2_hidden('#skF_2'(A_2576,B_2577,C_2578),C_2578)
      | ~ r1_xboole_0(B_2577,u1_struct_0(A_2576))
      | ~ v3_pre_topc(u1_struct_0(A_2576),A_2576)
      | k2_pre_topc(A_2576,B_2577) = C_2578
      | ~ m1_subset_1(C_2578,k1_zfmisc_1(u1_struct_0(A_2576)))
      | ~ m1_subset_1(B_2577,k1_zfmisc_1(u1_struct_0(A_2576)))
      | ~ l1_pre_topc(A_2576) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_38730])).

tff(c_40227,plain,(
    ! [B_2577,C_2578] :
      ( r2_hidden('#skF_2'('#skF_5',B_2577,C_2578),C_2578)
      | ~ r1_xboole_0(B_2577,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_2577) = C_2578
      | ~ m1_subset_1(C_2578,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2577,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_40223])).

tff(c_40519,plain,(
    ! [B_2583,C_2584] :
      ( r2_hidden('#skF_2'('#skF_5',B_2583,C_2584),C_2584)
      | ~ r1_xboole_0(B_2583,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2583) = C_2584
      | ~ m1_subset_1(C_2584,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2583,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_35958,c_35061,c_40227])).

tff(c_40534,plain,(
    ! [B_2583] :
      ( r2_hidden('#skF_2'('#skF_5',B_2583,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_2583,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2583) = '#skF_7'
      | ~ m1_subset_1(B_2583,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_40519])).

tff(c_40554,plain,(
    ! [B_2585] :
      ( ~ r1_xboole_0(B_2585,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2585) = '#skF_7'
      | ~ m1_subset_1(B_2585,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36869,c_40534])).

tff(c_40588,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_40554])).

tff(c_40601,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35772,c_40588])).

tff(c_40602,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_40601])).

tff(c_40605,plain,(
    k4_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_40602])).

tff(c_40612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40605])).

tff(c_40614,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_35971])).

tff(c_35961,plain,(
    ! [C_2249] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2249,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2249,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35932,c_35959])).

tff(c_35967,plain,(
    ! [C_2249] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2249,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2249,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_35961])).

tff(c_40640,plain,(
    ! [C_2249] :
      ( ~ r2_hidden(C_2249,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2249,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40614,c_35967])).

tff(c_40765,plain,(
    ! [B_2612,C_2613] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_2612,C_2613),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2612) = C_2613
      | ~ m1_subset_1(C_2613,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2612,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_40740,c_40640])).

tff(c_40791,plain,(
    ! [B_2617,C_2618] :
      ( k2_pre_topc('#skF_5',B_2617) = C_2618
      | ~ m1_subset_1(C_2618,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2617,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_40750,c_40765])).

tff(c_40806,plain,(
    ! [B_2619] :
      ( k2_pre_topc('#skF_5',B_2619) = '#skF_7'
      | ~ m1_subset_1(B_2619,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_40791])).

tff(c_40809,plain,(
    k2_pre_topc('#skF_5','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_35068,c_40806])).

tff(c_40824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35842,c_40809])).

tff(c_40825,plain,(
    k2_pre_topc('#skF_5','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_35565])).

tff(c_35518,plain,(
    ! [B_2218,A_2219] :
      ( v1_tops_1(B_2218,A_2219)
      | k2_pre_topc(A_2219,B_2218) != k2_struct_0(A_2219)
      | ~ m1_subset_1(B_2218,k1_zfmisc_1(u1_struct_0(A_2219)))
      | ~ l1_pre_topc(A_2219) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_35521,plain,(
    ! [B_2218] :
      ( v1_tops_1(B_2218,'#skF_5')
      | k2_pre_topc('#skF_5',B_2218) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_2218,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35518])).

tff(c_40992,plain,(
    ! [B_2629] :
      ( v1_tops_1(B_2629,'#skF_5')
      | k2_pre_topc('#skF_5',B_2629) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_2629,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35521])).

tff(c_40995,plain,
    ( v1_tops_1('#skF_7','#skF_5')
    | k2_pre_topc('#skF_5','#skF_7') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_35068,c_40992])).

tff(c_41008,plain,
    ( v1_tops_1('#skF_7','#skF_5')
    | k2_struct_0('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40825,c_40995])).

tff(c_41033,plain,(
    k2_struct_0('#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_41008])).

tff(c_45714,plain,(
    ! [A_2988,B_2989,C_2990] :
      ( r2_hidden('#skF_2'(A_2988,B_2989,C_2990),u1_struct_0(A_2988))
      | k2_pre_topc(A_2988,B_2989) = C_2990
      | ~ m1_subset_1(C_2990,k1_zfmisc_1(u1_struct_0(A_2988)))
      | ~ m1_subset_1(B_2989,k1_zfmisc_1(u1_struct_0(A_2988)))
      | ~ l1_pre_topc(A_2988) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_45722,plain,(
    ! [B_2989,C_2990] :
      ( r2_hidden('#skF_2'('#skF_5',B_2989,C_2990),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2989) = C_2990
      | ~ m1_subset_1(C_2990,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2989,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_45714])).

tff(c_45739,plain,(
    ! [B_2993,C_2994] :
      ( r2_hidden('#skF_2'('#skF_5',B_2993,C_2994),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2993) = C_2994
      | ~ m1_subset_1(C_2994,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2993,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_45722])).

tff(c_45745,plain,(
    ! [B_2993,C_2994] :
      ( m1_subset_1('#skF_2'('#skF_5',B_2993,C_2994),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2993) = C_2994
      | ~ m1_subset_1(C_2994,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2993,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_45739,c_35375])).

tff(c_45726,plain,(
    ! [B_2989,C_2990] :
      ( r2_hidden('#skF_2'('#skF_5',B_2989,C_2990),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2989) = C_2990
      | ~ m1_subset_1(C_2990,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2989,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_45722])).

tff(c_40832,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35568])).

tff(c_40856,plain,(
    ! [B_2621,A_2622] :
      ( v4_pre_topc(B_2621,A_2622)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_2622),B_2621),A_2622)
      | ~ m1_subset_1(B_2621,k1_zfmisc_1(u1_struct_0(A_2622)))
      | ~ l1_pre_topc(A_2622) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_40864,plain,(
    ! [A_2622] :
      ( v4_pre_topc(k1_xboole_0,A_2622)
      | ~ v3_pre_topc(u1_struct_0(A_2622),A_2622)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_2622)))
      | ~ l1_pre_topc(A_2622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_40856])).

tff(c_40944,plain,(
    ! [A_2627] :
      ( v4_pre_topc(k1_xboole_0,A_2627)
      | ~ v3_pre_topc(u1_struct_0(A_2627),A_2627)
      | ~ l1_pre_topc(A_2627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40864])).

tff(c_40947,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_40944])).

tff(c_40949,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_40947])).

tff(c_40950,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40832,c_40949])).

tff(c_40974,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_40950])).

tff(c_40978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_40974])).

tff(c_40979,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_35568])).

tff(c_40980,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_35568])).

tff(c_41184,plain,(
    ! [A_2642,B_2643] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_2642),B_2643),A_2642)
      | ~ v4_pre_topc(B_2643,A_2642)
      | ~ m1_subset_1(B_2643,k1_zfmisc_1(u1_struct_0(A_2642)))
      | ~ l1_pre_topc(A_2642) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_41195,plain,(
    ! [A_2642] :
      ( v3_pre_topc(u1_struct_0(A_2642),A_2642)
      | ~ v4_pre_topc(k1_xboole_0,A_2642)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_2642)))
      | ~ l1_pre_topc(A_2642) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_41184])).

tff(c_41221,plain,(
    ! [A_2645] :
      ( v3_pre_topc(u1_struct_0(A_2645),A_2645)
      | ~ v4_pre_topc(k1_xboole_0,A_2645)
      | ~ l1_pre_topc(A_2645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_41195])).

tff(c_41227,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_41221])).

tff(c_41230,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_40980,c_41227])).

tff(c_43050,plain,(
    ! [A_2849,B_2850,C_2851,E_2852] :
      ( v3_pre_topc('#skF_3'(A_2849,B_2850,C_2851),A_2849)
      | ~ r1_xboole_0(B_2850,E_2852)
      | ~ r2_hidden('#skF_2'(A_2849,B_2850,C_2851),E_2852)
      | ~ v3_pre_topc(E_2852,A_2849)
      | ~ m1_subset_1(E_2852,k1_zfmisc_1(u1_struct_0(A_2849)))
      | k2_pre_topc(A_2849,B_2850) = C_2851
      | ~ m1_subset_1(C_2851,k1_zfmisc_1(u1_struct_0(A_2849)))
      | ~ m1_subset_1(B_2850,k1_zfmisc_1(u1_struct_0(A_2849)))
      | ~ l1_pre_topc(A_2849) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_43090,plain,(
    ! [A_26,B_70,C_92] :
      ( v3_pre_topc('#skF_3'(A_26,B_70,C_92),A_26)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_43050])).

tff(c_44985,plain,(
    ! [A_2955,B_2956,C_2957] :
      ( v3_pre_topc('#skF_3'(A_2955,B_2956,C_2957),A_2955)
      | ~ r1_xboole_0(B_2956,u1_struct_0(A_2955))
      | ~ v3_pre_topc(u1_struct_0(A_2955),A_2955)
      | k2_pre_topc(A_2955,B_2956) = C_2957
      | ~ m1_subset_1(C_2957,k1_zfmisc_1(u1_struct_0(A_2955)))
      | ~ m1_subset_1(B_2956,k1_zfmisc_1(u1_struct_0(A_2955)))
      | ~ l1_pre_topc(A_2955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_43090])).

tff(c_44989,plain,(
    ! [B_2956,C_2957] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_2956,C_2957),'#skF_5')
      | ~ r1_xboole_0(B_2956,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_2956) = C_2957
      | ~ m1_subset_1(C_2957,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2956,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_44985])).

tff(c_45113,plain,(
    ! [B_2965,C_2966] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_2965,C_2966),'#skF_5')
      | ~ r1_xboole_0(B_2965,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2965) = C_2966
      | ~ m1_subset_1(C_2966,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2965,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_41230,c_35061,c_44989])).

tff(c_45196,plain,(
    ! [B_2969] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_2969,'#skF_7'),'#skF_5')
      | ~ r1_xboole_0(B_2969,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2969) = '#skF_7'
      | ~ m1_subset_1(B_2969,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_45113])).

tff(c_45229,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_45196])).

tff(c_45243,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40979,c_45229])).

tff(c_45244,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_45243])).

tff(c_45245,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_45244])).

tff(c_45248,plain,(
    k4_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_45245])).

tff(c_45255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_45248])).

tff(c_45257,plain,(
    r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_45244])).

tff(c_41268,plain,(
    ! [A_2648,C_2649,B_2650] :
      ( ~ v2_struct_0(A_2648)
      | ~ r2_hidden(C_2649,k2_pre_topc(A_2648,B_2650))
      | ~ m1_subset_1(C_2649,u1_struct_0(A_2648))
      | ~ m1_subset_1(B_2650,k1_zfmisc_1(u1_struct_0(A_2648)))
      | ~ l1_pre_topc(A_2648) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_41274,plain,(
    ! [C_2649] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2649,k1_xboole_0)
      | ~ m1_subset_1(C_2649,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40979,c_41268])).

tff(c_41282,plain,(
    ! [C_2649] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2649,k1_xboole_0)
      | ~ m1_subset_1(C_2649,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_35061,c_35061,c_41274])).

tff(c_41285,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_41282])).

tff(c_41035,plain,(
    ! [B_2632] :
      ( k2_pre_topc('#skF_5',B_2632) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_2632,'#skF_5')
      | ~ m1_subset_1(B_2632,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_41041,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_41035])).

tff(c_41055,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_41041])).

tff(c_41525,plain,(
    ! [C_2693,A_2694,B_2695] :
      ( r2_hidden(C_2693,'#skF_4'(A_2694,B_2695,C_2693))
      | r2_hidden(C_2693,k2_pre_topc(A_2694,B_2695))
      | v2_struct_0(A_2694)
      | ~ m1_subset_1(C_2693,u1_struct_0(A_2694))
      | ~ m1_subset_1(B_2695,k1_zfmisc_1(u1_struct_0(A_2694)))
      | ~ l1_pre_topc(A_2694) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_41527,plain,(
    ! [C_2693,B_2695] :
      ( r2_hidden(C_2693,'#skF_4'('#skF_5',B_2695,C_2693))
      | r2_hidden(C_2693,k2_pre_topc('#skF_5',B_2695))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_2693,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2695,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_41525])).

tff(c_41535,plain,(
    ! [C_2693,B_2695] :
      ( r2_hidden(C_2693,'#skF_4'('#skF_5',B_2695,C_2693))
      | r2_hidden(C_2693,k2_pre_topc('#skF_5',B_2695))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_2693,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2695,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_41527])).

tff(c_41713,plain,(
    ! [C_2720,B_2721] :
      ( r2_hidden(C_2720,'#skF_4'('#skF_5',B_2721,C_2720))
      | r2_hidden(C_2720,k2_pre_topc('#skF_5',B_2721))
      | ~ m1_subset_1(C_2720,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_2721,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41285,c_41535])).

tff(c_41717,plain,(
    ! [C_2720] :
      ( r2_hidden(C_2720,'#skF_4'('#skF_5','#skF_6',C_2720))
      | r2_hidden(C_2720,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_2720,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_35062,c_41713])).

tff(c_41777,plain,(
    ! [C_2728] :
      ( r2_hidden(C_2728,'#skF_4'('#skF_5','#skF_6',C_2728))
      | r2_hidden(C_2728,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2728,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41055,c_41717])).

tff(c_42064,plain,(
    ! [C_2751,A_2752] :
      ( r2_hidden(C_2751,A_2752)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_2751),k1_zfmisc_1(A_2752))
      | r2_hidden(C_2751,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2751,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_41777,c_26])).

tff(c_42068,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_42064])).

tff(c_42075,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_41055,c_35061,c_42068])).

tff(c_42076,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41285,c_42075])).

tff(c_42123,plain,(
    ! [B_2760,D_2761,C_2762,A_2763] :
      ( ~ r1_xboole_0(B_2760,D_2761)
      | ~ r2_hidden(C_2762,D_2761)
      | ~ v3_pre_topc(D_2761,A_2763)
      | ~ m1_subset_1(D_2761,k1_zfmisc_1(u1_struct_0(A_2763)))
      | ~ r2_hidden(C_2762,k2_pre_topc(A_2763,B_2760))
      | ~ m1_subset_1(C_2762,u1_struct_0(A_2763))
      | ~ m1_subset_1(B_2760,k1_zfmisc_1(u1_struct_0(A_2763)))
      | ~ l1_pre_topc(A_2763) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42253,plain,(
    ! [C_2768,A_2769] :
      ( ~ r2_hidden(C_2768,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_2769)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_2769)))
      | ~ r2_hidden(C_2768,k2_pre_topc(A_2769,'#skF_6'))
      | ~ m1_subset_1(C_2768,u1_struct_0(A_2769))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2769)))
      | ~ l1_pre_topc(A_2769) ) ),
    inference(resolution,[status(thm)],[c_35050,c_42123])).

tff(c_42255,plain,(
    ! [C_2768] :
      ( ~ r2_hidden(C_2768,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_2768,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_2768,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_42253])).

tff(c_42258,plain,(
    ! [C_2770] :
      ( ~ r2_hidden(C_2770,'#skF_7')
      | ~ r2_hidden(C_2770,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2770,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_41055,c_35068,c_35048,c_42255])).

tff(c_42267,plain,(
    ! [C_2771] :
      ( ~ r2_hidden(C_2771,'#skF_7')
      | ~ m1_subset_1(C_2771,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42076,c_42258])).

tff(c_42278,plain,(
    ! [A_2199] : ~ r2_hidden(A_2199,'#skF_7') ),
    inference(resolution,[status(thm)],[c_35373,c_42267])).

tff(c_43308,plain,(
    ! [A_2869,B_2870,C_2871,E_2872] :
      ( r2_hidden('#skF_2'(A_2869,B_2870,C_2871),C_2871)
      | ~ r1_xboole_0(B_2870,E_2872)
      | ~ r2_hidden('#skF_2'(A_2869,B_2870,C_2871),E_2872)
      | ~ v3_pre_topc(E_2872,A_2869)
      | ~ m1_subset_1(E_2872,k1_zfmisc_1(u1_struct_0(A_2869)))
      | k2_pre_topc(A_2869,B_2870) = C_2871
      | ~ m1_subset_1(C_2871,k1_zfmisc_1(u1_struct_0(A_2869)))
      | ~ m1_subset_1(B_2870,k1_zfmisc_1(u1_struct_0(A_2869)))
      | ~ l1_pre_topc(A_2869) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_43356,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_43308])).

tff(c_45278,plain,(
    ! [A_2970,B_2971,C_2972] :
      ( r2_hidden('#skF_2'(A_2970,B_2971,C_2972),C_2972)
      | ~ r1_xboole_0(B_2971,u1_struct_0(A_2970))
      | ~ v3_pre_topc(u1_struct_0(A_2970),A_2970)
      | k2_pre_topc(A_2970,B_2971) = C_2972
      | ~ m1_subset_1(C_2972,k1_zfmisc_1(u1_struct_0(A_2970)))
      | ~ m1_subset_1(B_2971,k1_zfmisc_1(u1_struct_0(A_2970)))
      | ~ l1_pre_topc(A_2970) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_43356])).

tff(c_45282,plain,(
    ! [B_2971,C_2972] :
      ( r2_hidden('#skF_2'('#skF_5',B_2971,C_2972),C_2972)
      | ~ r1_xboole_0(B_2971,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_2971) = C_2972
      | ~ m1_subset_1(C_2972,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2971,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_45278])).

tff(c_45614,plain,(
    ! [B_2982,C_2983] :
      ( r2_hidden('#skF_2'('#skF_5',B_2982,C_2983),C_2983)
      | ~ r1_xboole_0(B_2982,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2982) = C_2983
      | ~ m1_subset_1(C_2983,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2982,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_41230,c_35061,c_45282])).

tff(c_45629,plain,(
    ! [B_2982] :
      ( r2_hidden('#skF_2'('#skF_5',B_2982,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_2982,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2982) = '#skF_7'
      | ~ m1_subset_1(B_2982,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_45614])).

tff(c_45650,plain,(
    ! [B_2984] :
      ( ~ r1_xboole_0(B_2984,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2984) = '#skF_7'
      | ~ m1_subset_1(B_2984,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42278,c_45629])).

tff(c_45683,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_45650])).

tff(c_45698,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40979,c_45257,c_45683])).

tff(c_45700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_45698])).

tff(c_45702,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_41282])).

tff(c_41272,plain,(
    ! [C_2649] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2649,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2649,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41055,c_41268])).

tff(c_41280,plain,(
    ! [C_2649] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_2649,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2649,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_41272])).

tff(c_45749,plain,(
    ! [C_2995] :
      ( ~ r2_hidden(C_2995,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_2995,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45702,c_41280])).

tff(c_45770,plain,(
    ! [B_3002,C_3003] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_3002,C_3003),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3002) = C_3003
      | ~ m1_subset_1(C_3003,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3002,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_45726,c_45749])).

tff(c_45792,plain,(
    ! [B_3007,C_3008] :
      ( k2_pre_topc('#skF_5',B_3007) = C_3008
      | ~ m1_subset_1(C_3008,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3007,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_45745,c_45770])).

tff(c_45807,plain,(
    ! [B_3009] :
      ( k2_pre_topc('#skF_5',B_3009) = '#skF_7'
      | ~ m1_subset_1(B_3009,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_45792])).

tff(c_45824,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_35062,c_45807])).

tff(c_45827,plain,(
    k2_struct_0('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45824,c_41055])).

tff(c_45829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41033,c_45827])).

tff(c_45831,plain,(
    k2_struct_0('#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_41008])).

tff(c_35504,plain,(
    ! [A_2216] :
      ( k2_pre_topc(A_2216,u1_struct_0(A_2216)) = k2_struct_0(A_2216)
      | ~ v1_tops_1(u1_struct_0(A_2216),A_2216)
      | ~ l1_pre_topc(A_2216) ) ),
    inference(resolution,[status(thm)],[c_121,c_35484])).

tff(c_35507,plain,
    ( k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35504])).

tff(c_35509,plain,
    ( k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35507])).

tff(c_35510,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35509])).

tff(c_35539,plain,(
    ! [A_2221] :
      ( v1_tops_1(u1_struct_0(A_2221),A_2221)
      | k2_pre_topc(A_2221,u1_struct_0(A_2221)) != k2_struct_0(A_2221)
      | ~ l1_pre_topc(A_2221) ) ),
    inference(resolution,[status(thm)],[c_121,c_35518])).

tff(c_35545,plain,
    ( v1_tops_1(k2_struct_0('#skF_5'),'#skF_5')
    | k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) != k2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_35539])).

tff(c_35548,plain,
    ( v1_tops_1(k2_struct_0('#skF_5'),'#skF_5')
    | k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35545])).

tff(c_35549,plain,(
    k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_35510,c_35548])).

tff(c_45858,plain,(
    k2_pre_topc('#skF_5','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45831,c_45831,c_35549])).

tff(c_45877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40825,c_45858])).

tff(c_45878,plain,(
    k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_35509])).

tff(c_46432,plain,(
    ! [C_3051] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3051,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3051,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45878,c_46424])).

tff(c_46440,plain,(
    ! [C_3051] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3051,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3051,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_121,c_35061,c_35061,c_46432])).

tff(c_51852,plain,(
    ! [C_3051] :
      ( ~ r2_hidden(C_3051,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3051,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51839,c_46440])).

tff(c_51942,plain,(
    ! [B_3416,C_3417] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_3416,C_3417),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3416) = C_3417
      | ~ m1_subset_1(C_3417,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3416,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_51905,c_51852])).

tff(c_51955,plain,(
    ! [B_3418,C_3419] :
      ( k2_pre_topc('#skF_5',B_3418) = C_3419
      | ~ m1_subset_1(C_3419,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3418,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_51915,c_51942])).

tff(c_51970,plain,(
    ! [B_3420] :
      ( k2_pre_topc('#skF_5',B_3420) = '#skF_7'
      | ~ m1_subset_1(B_3420,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_51955])).

tff(c_51973,plain,(
    k2_pre_topc('#skF_5','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_35068,c_51970])).

tff(c_51988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46215,c_51973])).

tff(c_51989,plain,(
    k2_pre_topc('#skF_5','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_45936])).

tff(c_45890,plain,(
    ! [B_3012,A_3013] :
      ( v1_tops_1(B_3012,A_3013)
      | k2_pre_topc(A_3013,B_3012) != k2_struct_0(A_3013)
      | ~ m1_subset_1(B_3012,k1_zfmisc_1(u1_struct_0(A_3013)))
      | ~ l1_pre_topc(A_3013) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_45893,plain,(
    ! [B_3012] :
      ( v1_tops_1(B_3012,'#skF_5')
      | k2_pre_topc('#skF_5',B_3012) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_3012,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_45890])).

tff(c_52182,plain,(
    ! [B_3432] :
      ( v1_tops_1(B_3432,'#skF_5')
      | k2_pre_topc('#skF_5',B_3432) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_3432,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_45893])).

tff(c_52185,plain,
    ( v1_tops_1('#skF_7','#skF_5')
    | k2_pre_topc('#skF_5','#skF_7') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_35068,c_52182])).

tff(c_52198,plain,
    ( v1_tops_1('#skF_7','#skF_5')
    | k2_struct_0('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51989,c_52185])).

tff(c_52224,plain,(
    k2_struct_0('#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_52198])).

tff(c_57181,plain,(
    ! [A_3814,B_3815,C_3816] :
      ( r2_hidden('#skF_2'(A_3814,B_3815,C_3816),u1_struct_0(A_3814))
      | k2_pre_topc(A_3814,B_3815) = C_3816
      | ~ m1_subset_1(C_3816,k1_zfmisc_1(u1_struct_0(A_3814)))
      | ~ m1_subset_1(B_3815,k1_zfmisc_1(u1_struct_0(A_3814)))
      | ~ l1_pre_topc(A_3814) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57189,plain,(
    ! [B_3815,C_3816] :
      ( r2_hidden('#skF_2'('#skF_5',B_3815,C_3816),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3815) = C_3816
      | ~ m1_subset_1(C_3816,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3815,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_57181])).

tff(c_57221,plain,(
    ! [B_3822,C_3823] :
      ( r2_hidden('#skF_2'('#skF_5',B_3822,C_3823),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3822) = C_3823
      | ~ m1_subset_1(C_3823,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3822,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_57189])).

tff(c_57231,plain,(
    ! [B_3822,C_3823] :
      ( m1_subset_1('#skF_2'('#skF_5',B_3822,C_3823),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3822) = C_3823
      | ~ m1_subset_1(C_3823,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3822,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_57221,c_35375])).

tff(c_51995,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_45940])).

tff(c_52075,plain,(
    ! [B_3426,A_3427] :
      ( v4_pre_topc(B_3426,A_3427)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_3427),B_3426),A_3427)
      | ~ m1_subset_1(B_3426,k1_zfmisc_1(u1_struct_0(A_3427)))
      | ~ l1_pre_topc(A_3427) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52083,plain,(
    ! [A_3427] :
      ( v4_pre_topc(k1_xboole_0,A_3427)
      | ~ v3_pre_topc(u1_struct_0(A_3427),A_3427)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_3427)))
      | ~ l1_pre_topc(A_3427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_52075])).

tff(c_52154,plain,(
    ! [A_3431] :
      ( v4_pre_topc(k1_xboole_0,A_3431)
      | ~ v3_pre_topc(u1_struct_0(A_3431),A_3431)
      | ~ l1_pre_topc(A_3431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52083])).

tff(c_52157,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_52154])).

tff(c_52159,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_52157])).

tff(c_52160,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_51995,c_52159])).

tff(c_52163,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_52160])).

tff(c_52167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_52163])).

tff(c_52168,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45940])).

tff(c_52169,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_45940])).

tff(c_52454,plain,(
    ! [A_3452,B_3453] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_3452),B_3453),A_3452)
      | ~ v4_pre_topc(B_3453,A_3452)
      | ~ m1_subset_1(B_3453,k1_zfmisc_1(u1_struct_0(A_3452)))
      | ~ l1_pre_topc(A_3452) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52465,plain,(
    ! [A_3452] :
      ( v3_pre_topc(u1_struct_0(A_3452),A_3452)
      | ~ v4_pre_topc(k1_xboole_0,A_3452)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_3452)))
      | ~ l1_pre_topc(A_3452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35293,c_52454])).

tff(c_52490,plain,(
    ! [A_3455] :
      ( v3_pre_topc(u1_struct_0(A_3455),A_3455)
      | ~ v4_pre_topc(k1_xboole_0,A_3455)
      | ~ l1_pre_topc(A_3455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52465])).

tff(c_52496,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_52490])).

tff(c_52499,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_52169,c_52496])).

tff(c_54789,plain,(
    ! [A_3689,B_3690,C_3691,E_3692] :
      ( v3_pre_topc('#skF_3'(A_3689,B_3690,C_3691),A_3689)
      | ~ r1_xboole_0(B_3690,E_3692)
      | ~ r2_hidden('#skF_2'(A_3689,B_3690,C_3691),E_3692)
      | ~ v3_pre_topc(E_3692,A_3689)
      | ~ m1_subset_1(E_3692,k1_zfmisc_1(u1_struct_0(A_3689)))
      | k2_pre_topc(A_3689,B_3690) = C_3691
      | ~ m1_subset_1(C_3691,k1_zfmisc_1(u1_struct_0(A_3689)))
      | ~ m1_subset_1(B_3690,k1_zfmisc_1(u1_struct_0(A_3689)))
      | ~ l1_pre_topc(A_3689) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54829,plain,(
    ! [A_26,B_70,C_92] :
      ( v3_pre_topc('#skF_3'(A_26,B_70,C_92),A_26)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_54789])).

tff(c_56248,plain,(
    ! [A_3768,B_3769,C_3770] :
      ( v3_pre_topc('#skF_3'(A_3768,B_3769,C_3770),A_3768)
      | ~ r1_xboole_0(B_3769,u1_struct_0(A_3768))
      | ~ v3_pre_topc(u1_struct_0(A_3768),A_3768)
      | k2_pre_topc(A_3768,B_3769) = C_3770
      | ~ m1_subset_1(C_3770,k1_zfmisc_1(u1_struct_0(A_3768)))
      | ~ m1_subset_1(B_3769,k1_zfmisc_1(u1_struct_0(A_3768)))
      | ~ l1_pre_topc(A_3768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54829])).

tff(c_56252,plain,(
    ! [B_3769,C_3770] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3769,C_3770),'#skF_5')
      | ~ r1_xboole_0(B_3769,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_3769) = C_3770
      | ~ m1_subset_1(C_3770,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3769,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_56248])).

tff(c_56309,plain,(
    ! [B_3780,C_3781] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3780,C_3781),'#skF_5')
      | ~ r1_xboole_0(B_3780,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3780) = C_3781
      | ~ m1_subset_1(C_3781,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3780,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_52499,c_35061,c_56252])).

tff(c_56343,plain,(
    ! [B_3782] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_3782,'#skF_7'),'#skF_5')
      | ~ r1_xboole_0(B_3782,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3782) = '#skF_7'
      | ~ m1_subset_1(B_3782,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_56309])).

tff(c_56376,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_56343])).

tff(c_56392,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52168,c_56376])).

tff(c_56393,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_7'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_56392])).

tff(c_56394,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56393])).

tff(c_56397,plain,(
    k4_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_56394])).

tff(c_56404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_56397])).

tff(c_56406,plain,(
    r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56393])).

tff(c_52557,plain,(
    ! [A_3459,C_3460,B_3461] :
      ( ~ v2_struct_0(A_3459)
      | ~ r2_hidden(C_3460,k2_pre_topc(A_3459,B_3461))
      | ~ m1_subset_1(C_3460,u1_struct_0(A_3459))
      | ~ m1_subset_1(B_3461,k1_zfmisc_1(u1_struct_0(A_3459)))
      | ~ l1_pre_topc(A_3459) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52563,plain,(
    ! [C_3460] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3460,k1_xboole_0)
      | ~ m1_subset_1(C_3460,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52168,c_52557])).

tff(c_52573,plain,(
    ! [C_3460] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3460,k1_xboole_0)
      | ~ m1_subset_1(C_3460,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_35061,c_35061,c_52563])).

tff(c_52578,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52573])).

tff(c_52226,plain,(
    ! [B_3435] :
      ( k2_pre_topc('#skF_5',B_3435) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_3435,'#skF_5')
      | ~ m1_subset_1(B_3435,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_52232,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_52226])).

tff(c_52246,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_52232])).

tff(c_52723,plain,(
    ! [C_3483,A_3484,B_3485] :
      ( r2_hidden(C_3483,'#skF_4'(A_3484,B_3485,C_3483))
      | r2_hidden(C_3483,k2_pre_topc(A_3484,B_3485))
      | v2_struct_0(A_3484)
      | ~ m1_subset_1(C_3483,u1_struct_0(A_3484))
      | ~ m1_subset_1(B_3485,k1_zfmisc_1(u1_struct_0(A_3484)))
      | ~ l1_pre_topc(A_3484) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52725,plain,(
    ! [C_3483,B_3485] :
      ( r2_hidden(C_3483,'#skF_4'('#skF_5',B_3485,C_3483))
      | r2_hidden(C_3483,k2_pre_topc('#skF_5',B_3485))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3483,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3485,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_52723])).

tff(c_52733,plain,(
    ! [C_3483,B_3485] :
      ( r2_hidden(C_3483,'#skF_4'('#skF_5',B_3485,C_3483))
      | r2_hidden(C_3483,k2_pre_topc('#skF_5',B_3485))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3483,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3485,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_52725])).

tff(c_52965,plain,(
    ! [C_3518,B_3519] :
      ( r2_hidden(C_3518,'#skF_4'('#skF_5',B_3519,C_3518))
      | r2_hidden(C_3518,k2_pre_topc('#skF_5',B_3519))
      | ~ m1_subset_1(C_3518,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3519,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52578,c_52733])).

tff(c_52969,plain,(
    ! [C_3518] :
      ( r2_hidden(C_3518,'#skF_4'('#skF_5','#skF_6',C_3518))
      | r2_hidden(C_3518,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_3518,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_35062,c_52965])).

tff(c_53000,plain,(
    ! [C_3523] :
      ( r2_hidden(C_3523,'#skF_4'('#skF_5','#skF_6',C_3523))
      | r2_hidden(C_3523,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3523,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52246,c_52969])).

tff(c_53199,plain,(
    ! [C_3542,A_3543] :
      ( r2_hidden(C_3542,A_3543)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_3542),k1_zfmisc_1(A_3543))
      | r2_hidden(C_3542,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3542,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53000,c_26])).

tff(c_53203,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_53199])).

tff(c_53210,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_52246,c_35061,c_53203])).

tff(c_53211,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52578,c_53210])).

tff(c_53387,plain,(
    ! [B_3568,D_3569,C_3570,A_3571] :
      ( ~ r1_xboole_0(B_3568,D_3569)
      | ~ r2_hidden(C_3570,D_3569)
      | ~ v3_pre_topc(D_3569,A_3571)
      | ~ m1_subset_1(D_3569,k1_zfmisc_1(u1_struct_0(A_3571)))
      | ~ r2_hidden(C_3570,k2_pre_topc(A_3571,B_3568))
      | ~ m1_subset_1(C_3570,u1_struct_0(A_3571))
      | ~ m1_subset_1(B_3568,k1_zfmisc_1(u1_struct_0(A_3571)))
      | ~ l1_pre_topc(A_3571) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_53469,plain,(
    ! [C_3575,A_3576] :
      ( ~ r2_hidden(C_3575,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_3576)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3576)))
      | ~ r2_hidden(C_3575,k2_pre_topc(A_3576,'#skF_6'))
      | ~ m1_subset_1(C_3575,u1_struct_0(A_3576))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_3576)))
      | ~ l1_pre_topc(A_3576) ) ),
    inference(resolution,[status(thm)],[c_35050,c_53387])).

tff(c_53471,plain,(
    ! [C_3575] :
      ( ~ r2_hidden(C_3575,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_3575,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_3575,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_53469])).

tff(c_53474,plain,(
    ! [C_3577] :
      ( ~ r2_hidden(C_3577,'#skF_7')
      | ~ r2_hidden(C_3577,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3577,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35062,c_35061,c_35061,c_52246,c_35068,c_35048,c_53471])).

tff(c_53483,plain,(
    ! [C_3578] :
      ( ~ r2_hidden(C_3578,'#skF_7')
      | ~ m1_subset_1(C_3578,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53211,c_53474])).

tff(c_53494,plain,(
    ! [A_2199] : ~ r2_hidden(A_2199,'#skF_7') ),
    inference(resolution,[status(thm)],[c_35373,c_53483])).

tff(c_54678,plain,(
    ! [A_3680,B_3681,C_3682,E_3683] :
      ( r2_hidden('#skF_2'(A_3680,B_3681,C_3682),C_3682)
      | ~ r1_xboole_0(B_3681,E_3683)
      | ~ r2_hidden('#skF_2'(A_3680,B_3681,C_3682),E_3683)
      | ~ v3_pre_topc(E_3683,A_3680)
      | ~ m1_subset_1(E_3683,k1_zfmisc_1(u1_struct_0(A_3680)))
      | k2_pre_topc(A_3680,B_3681) = C_3682
      | ~ m1_subset_1(C_3682,k1_zfmisc_1(u1_struct_0(A_3680)))
      | ~ m1_subset_1(B_3681,k1_zfmisc_1(u1_struct_0(A_3680)))
      | ~ l1_pre_topc(A_3680) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54724,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_34,c_54678])).

tff(c_56605,plain,(
    ! [A_3787,B_3788,C_3789] :
      ( r2_hidden('#skF_2'(A_3787,B_3788,C_3789),C_3789)
      | ~ r1_xboole_0(B_3788,u1_struct_0(A_3787))
      | ~ v3_pre_topc(u1_struct_0(A_3787),A_3787)
      | k2_pre_topc(A_3787,B_3788) = C_3789
      | ~ m1_subset_1(C_3789,k1_zfmisc_1(u1_struct_0(A_3787)))
      | ~ m1_subset_1(B_3788,k1_zfmisc_1(u1_struct_0(A_3787)))
      | ~ l1_pre_topc(A_3787) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54724])).

tff(c_56609,plain,(
    ! [B_3788,C_3789] :
      ( r2_hidden('#skF_2'('#skF_5',B_3788,C_3789),C_3789)
      | ~ r1_xboole_0(B_3788,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_3788) = C_3789
      | ~ m1_subset_1(C_3789,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3788,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35061,c_56605])).

tff(c_57079,plain,(
    ! [B_3808,C_3809] :
      ( r2_hidden('#skF_2'('#skF_5',B_3808,C_3809),C_3809)
      | ~ r1_xboole_0(B_3808,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3808) = C_3809
      | ~ m1_subset_1(C_3809,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3808,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35061,c_35061,c_52499,c_35061,c_56609])).

tff(c_57094,plain,(
    ! [B_3808] :
      ( r2_hidden('#skF_2'('#skF_5',B_3808,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_3808,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3808) = '#skF_7'
      | ~ m1_subset_1(B_3808,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_57079])).

tff(c_57115,plain,(
    ! [B_3810] :
      ( ~ r1_xboole_0(B_3810,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3810) = '#skF_7'
      | ~ m1_subset_1(B_3810,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_53494,c_57094])).

tff(c_57148,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_57115])).

tff(c_57165,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52168,c_56406,c_57148])).

tff(c_57167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_57165])).

tff(c_57169,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_52573])).

tff(c_52567,plain,(
    ! [C_3460] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3460,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3460,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45878,c_52557])).

tff(c_52577,plain,(
    ! [C_3460] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3460,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3460,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_121,c_35061,c_35061,c_52567])).

tff(c_57207,plain,(
    ! [C_3460] :
      ( ~ r2_hidden(C_3460,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_3460,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57169,c_52577])).

tff(c_57259,plain,(
    ! [B_3835,C_3836] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_3835,C_3836),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_3835) = C_3836
      | ~ m1_subset_1(C_3836,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3835,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_57221,c_57207])).

tff(c_57268,plain,(
    ! [B_3837,C_3838] :
      ( k2_pre_topc('#skF_5',B_3837) = C_3838
      | ~ m1_subset_1(C_3838,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3837,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_57231,c_57259])).

tff(c_57283,plain,(
    ! [B_3839] :
      ( k2_pre_topc('#skF_5',B_3839) = '#skF_7'
      | ~ m1_subset_1(B_3839,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_35068,c_57268])).

tff(c_57300,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_35062,c_57283])).

tff(c_57303,plain,(
    k2_struct_0('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57300,c_52246])).

tff(c_57305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52224,c_57303])).

tff(c_57307,plain,(
    k2_struct_0('#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_52198])).

tff(c_57323,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57307,c_35062])).

tff(c_35497,plain,(
    ! [B_2214] :
      ( k2_pre_topc('#skF_5',B_2214) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_2214,'#skF_5')
      | ~ m1_subset_1(B_2214,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_57456,plain,(
    ! [B_3845] :
      ( k2_pre_topc('#skF_5',B_3845) = '#skF_7'
      | ~ v1_tops_1(B_3845,'#skF_5')
      | ~ m1_subset_1(B_3845,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57307,c_57307,c_35497])).

tff(c_57459,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_7'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_57323,c_57456])).

tff(c_57470,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_57459])).

tff(c_57324,plain,(
    u1_struct_0('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57307,c_35061])).

tff(c_70,plain,(
    ! [B_114,A_112] :
      ( v4_pre_topc(B_114,A_112)
      | k2_pre_topc(A_112,B_114) != B_114
      | ~ v2_pre_topc(A_112)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_57354,plain,(
    ! [B_114] :
      ( v4_pre_topc(B_114,'#skF_5')
      | k2_pre_topc('#skF_5',B_114) != B_114
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_114,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57324,c_70])).

tff(c_58614,plain,(
    ! [B_3978] :
      ( v4_pre_topc(B_3978,'#skF_5')
      | k2_pre_topc('#skF_5',B_3978) != B_3978
      | ~ m1_subset_1(B_3978,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_100,c_57354])).

tff(c_58617,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_57323,c_58614])).

tff(c_58627,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57470,c_58617])).

tff(c_58628,plain,(
    '#skF_7' != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52170,c_58627])).

tff(c_58542,plain,(
    ! [A_3972,B_3973,C_3974] :
      ( r2_hidden('#skF_2'(A_3972,B_3973,C_3974),u1_struct_0(A_3972))
      | k2_pre_topc(A_3972,B_3973) = C_3974
      | ~ m1_subset_1(C_3974,k1_zfmisc_1(u1_struct_0(A_3972)))
      | ~ m1_subset_1(B_3973,k1_zfmisc_1(u1_struct_0(A_3972)))
      | ~ l1_pre_topc(A_3972) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58550,plain,(
    ! [B_3973,C_3974] :
      ( r2_hidden('#skF_2'('#skF_5',B_3973,C_3974),'#skF_7')
      | k2_pre_topc('#skF_5',B_3973) = C_3974
      | ~ m1_subset_1(C_3974,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3973,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57324,c_58542])).

tff(c_58703,plain,(
    ! [B_3987,C_3988] :
      ( r2_hidden('#skF_2'('#skF_5',B_3987,C_3988),'#skF_7')
      | k2_pre_topc('#skF_5',B_3987) = C_3988
      | ~ m1_subset_1(C_3988,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3987,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_57324,c_57324,c_58550])).

tff(c_58713,plain,(
    ! [B_3987,C_3988] :
      ( m1_subset_1('#skF_2'('#skF_5',B_3987,C_3988),'#skF_7')
      | k2_pre_topc('#skF_5',B_3987) = C_3988
      | ~ m1_subset_1(C_3988,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3987,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58703,c_35375])).

tff(c_57631,plain,(
    ! [B_3861] :
      ( v4_pre_topc(B_3861,'#skF_5')
      | k2_pre_topc('#skF_5',B_3861) != B_3861
      | ~ m1_subset_1(B_3861,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_100,c_57354])).

tff(c_57634,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_57323,c_57631])).

tff(c_57644,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57470,c_57634])).

tff(c_57645,plain,(
    '#skF_7' != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52170,c_57644])).

tff(c_57513,plain,(
    ! [A_3849,C_3850,B_3851] :
      ( ~ v2_struct_0(A_3849)
      | ~ r2_hidden(C_3850,k2_pre_topc(A_3849,B_3851))
      | ~ m1_subset_1(C_3850,u1_struct_0(A_3849))
      | ~ m1_subset_1(B_3851,k1_zfmisc_1(u1_struct_0(A_3849)))
      | ~ l1_pre_topc(A_3849) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_57517,plain,(
    ! [C_3850] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3850,k1_xboole_0)
      | ~ m1_subset_1(C_3850,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52168,c_57513])).

tff(c_57523,plain,(
    ! [C_3850] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3850,k1_xboole_0)
      | ~ m1_subset_1(C_3850,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_57324,c_57517])).

tff(c_57526,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_57523])).

tff(c_57958,plain,(
    ! [A_3902,B_3903,C_3904] :
      ( m1_subset_1('#skF_4'(A_3902,B_3903,C_3904),k1_zfmisc_1(u1_struct_0(A_3902)))
      | r2_hidden(C_3904,k2_pre_topc(A_3902,B_3903))
      | v2_struct_0(A_3902)
      | ~ m1_subset_1(C_3904,u1_struct_0(A_3902))
      | ~ m1_subset_1(B_3903,k1_zfmisc_1(u1_struct_0(A_3902)))
      | ~ l1_pre_topc(A_3902) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_57672,plain,(
    ! [C_3863,A_3864,B_3865] :
      ( r2_hidden(C_3863,'#skF_4'(A_3864,B_3865,C_3863))
      | r2_hidden(C_3863,k2_pre_topc(A_3864,B_3865))
      | v2_struct_0(A_3864)
      | ~ m1_subset_1(C_3863,u1_struct_0(A_3864))
      | ~ m1_subset_1(B_3865,k1_zfmisc_1(u1_struct_0(A_3864)))
      | ~ l1_pre_topc(A_3864) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_57674,plain,(
    ! [C_3863,B_3865] :
      ( r2_hidden(C_3863,'#skF_4'('#skF_5',B_3865,C_3863))
      | r2_hidden(C_3863,k2_pre_topc('#skF_5',B_3865))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3863,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_3865,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57324,c_57672])).

tff(c_57682,plain,(
    ! [C_3863,B_3865] :
      ( r2_hidden(C_3863,'#skF_4'('#skF_5',B_3865,C_3863))
      | r2_hidden(C_3863,k2_pre_topc('#skF_5',B_3865))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3863,'#skF_7')
      | ~ m1_subset_1(B_3865,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_57324,c_57674])).

tff(c_57730,plain,(
    ! [C_3872,B_3873] :
      ( r2_hidden(C_3872,'#skF_4'('#skF_5',B_3873,C_3872))
      | r2_hidden(C_3872,k2_pre_topc('#skF_5',B_3873))
      | ~ m1_subset_1(C_3872,'#skF_7')
      | ~ m1_subset_1(B_3873,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57526,c_57682])).

tff(c_57749,plain,(
    ! [C_3872] :
      ( r2_hidden(C_3872,'#skF_4'('#skF_5','#skF_6',C_3872))
      | r2_hidden(C_3872,'#skF_7')
      | ~ m1_subset_1(C_3872,'#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57470,c_57730])).

tff(c_57801,plain,(
    ! [C_3879] :
      ( r2_hidden(C_3879,'#skF_4'('#skF_5','#skF_6',C_3879))
      | r2_hidden(C_3879,'#skF_7')
      | ~ m1_subset_1(C_3879,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57323,c_57749])).

tff(c_57808,plain,(
    ! [C_3879,A_16] :
      ( r2_hidden(C_3879,A_16)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_3879),k1_zfmisc_1(A_16))
      | r2_hidden(C_3879,'#skF_7')
      | ~ m1_subset_1(C_3879,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_57801,c_26])).

tff(c_57968,plain,(
    ! [C_3904] :
      ( r2_hidden(C_3904,u1_struct_0('#skF_5'))
      | r2_hidden(C_3904,'#skF_7')
      | ~ m1_subset_1(C_3904,'#skF_7')
      | r2_hidden(C_3904,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3904,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57958,c_57808])).

tff(c_58006,plain,(
    ! [C_3904] :
      ( r2_hidden(C_3904,'#skF_7')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_3904,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_57323,c_57324,c_57324,c_57470,c_57324,c_57968])).

tff(c_58007,plain,(
    ! [C_3904] :
      ( r2_hidden(C_3904,'#skF_7')
      | ~ m1_subset_1(C_3904,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57526,c_58006])).

tff(c_58369,plain,(
    ! [B_3948,D_3949,C_3950,A_3951] :
      ( ~ r1_xboole_0(B_3948,D_3949)
      | ~ r2_hidden(C_3950,D_3949)
      | ~ v3_pre_topc(D_3949,A_3951)
      | ~ m1_subset_1(D_3949,k1_zfmisc_1(u1_struct_0(A_3951)))
      | ~ r2_hidden(C_3950,k2_pre_topc(A_3951,B_3948))
      | ~ m1_subset_1(C_3950,u1_struct_0(A_3951))
      | ~ m1_subset_1(B_3948,k1_zfmisc_1(u1_struct_0(A_3951)))
      | ~ l1_pre_topc(A_3951) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58429,plain,(
    ! [C_3956,A_3957] :
      ( ~ r2_hidden(C_3956,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_3957)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3957)))
      | ~ r2_hidden(C_3956,k2_pre_topc(A_3957,'#skF_6'))
      | ~ m1_subset_1(C_3956,u1_struct_0(A_3957))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_3957)))
      | ~ l1_pre_topc(A_3957) ) ),
    inference(resolution,[status(thm)],[c_35050,c_58369])).

tff(c_58431,plain,(
    ! [C_3956] :
      ( ~ r2_hidden(C_3956,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
      | ~ r2_hidden(C_3956,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_3956,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57324,c_58429])).

tff(c_58434,plain,(
    ! [C_3958] :
      ( ~ r2_hidden(C_3958,'#skF_7')
      | ~ m1_subset_1(C_3958,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_57323,c_57324,c_57324,c_57470,c_121,c_35048,c_58431])).

tff(c_58448,plain,(
    ! [C_3904] : ~ m1_subset_1(C_3904,'#skF_7') ),
    inference(resolution,[status(thm)],[c_58007,c_58434])).

tff(c_57577,plain,(
    ! [A_3856,B_3857,C_3858] :
      ( r2_hidden('#skF_2'(A_3856,B_3857,C_3858),u1_struct_0(A_3856))
      | k2_pre_topc(A_3856,B_3857) = C_3858
      | ~ m1_subset_1(C_3858,k1_zfmisc_1(u1_struct_0(A_3856)))
      | ~ m1_subset_1(B_3857,k1_zfmisc_1(u1_struct_0(A_3856)))
      | ~ l1_pre_topc(A_3856) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57585,plain,(
    ! [B_3857,C_3858] :
      ( r2_hidden('#skF_2'('#skF_5',B_3857,C_3858),'#skF_7')
      | k2_pre_topc('#skF_5',B_3857) = C_3858
      | ~ m1_subset_1(C_3858,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_3857,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57324,c_57577])).

tff(c_57722,plain,(
    ! [B_3870,C_3871] :
      ( r2_hidden('#skF_2'('#skF_5',B_3870,C_3871),'#skF_7')
      | k2_pre_topc('#skF_5',B_3870) = C_3871
      | ~ m1_subset_1(C_3871,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3870,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_57324,c_57324,c_57585])).

tff(c_57728,plain,(
    ! [B_3870,C_3871] :
      ( m1_subset_1('#skF_2'('#skF_5',B_3870,C_3871),'#skF_7')
      | k2_pre_topc('#skF_5',B_3870) = C_3871
      | ~ m1_subset_1(C_3871,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3870,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_57722,c_35375])).

tff(c_58459,plain,(
    ! [B_3961,C_3962] :
      ( k2_pre_topc('#skF_5',B_3961) = C_3962
      | ~ m1_subset_1(C_3962,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3961,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58448,c_57728])).

tff(c_58471,plain,(
    ! [B_3963] :
      ( k2_pre_topc('#skF_5',B_3963) = '#skF_6'
      | ~ m1_subset_1(B_3963,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_57323,c_58459])).

tff(c_58483,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_57323,c_58471])).

tff(c_58499,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58483,c_57470])).

tff(c_58501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57645,c_58499])).

tff(c_58503,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_57523])).

tff(c_57519,plain,(
    ! [C_3850] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3850,'#skF_7')
      | ~ m1_subset_1(C_3850,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51989,c_57513])).

tff(c_57525,plain,(
    ! [C_3850] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_3850,'#skF_7')
      | ~ m1_subset_1(C_3850,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_121,c_57324,c_57324,c_57519])).

tff(c_58523,plain,(
    ! [C_3850] :
      ( ~ r2_hidden(C_3850,'#skF_7')
      | ~ m1_subset_1(C_3850,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58503,c_57525])).

tff(c_58729,plain,(
    ! [B_3994,C_3995] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_3994,C_3995),'#skF_7')
      | k2_pre_topc('#skF_5',B_3994) = C_3995
      | ~ m1_subset_1(C_3995,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3994,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58703,c_58523])).

tff(c_58734,plain,(
    ! [B_3996,C_3997] :
      ( k2_pre_topc('#skF_5',B_3996) = C_3997
      | ~ m1_subset_1(C_3997,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_3996,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58713,c_58729])).

tff(c_58746,plain,(
    ! [B_3998] :
      ( k2_pre_topc('#skF_5',B_3998) = '#skF_6'
      | ~ m1_subset_1(B_3998,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_57323,c_58734])).

tff(c_58758,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_57323,c_58746])).

tff(c_58761,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58758,c_57470])).

tff(c_58763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58628,c_58761])).

tff(c_58764,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_45937])).

tff(c_58810,plain,(
    ! [B_4002] :
      ( k2_pre_topc('#skF_5',B_4002) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_4002,'#skF_5')
      | ~ m1_subset_1(B_4002,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35487])).

tff(c_58816,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_35062,c_58810])).

tff(c_58829,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35046,c_58764,c_58816])).

tff(c_35289,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),'#skF_7') = k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_35068,c_35276])).

tff(c_35106,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(resolution,[status(thm)],[c_16,c_35096])).

tff(c_35443,plain,
    ( k3_xboole_0(k2_struct_0('#skF_5'),'#skF_7') = k1_xboole_0
    | k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') != k2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35289,c_35106])).

tff(c_35480,plain,(
    k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') != k2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35443])).

tff(c_35069,plain,(
    ! [A_2170,B_2171] :
      ( k4_xboole_0(A_2170,B_2171) = A_2170
      | ~ r1_xboole_0(A_2170,B_2171) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35076,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_35069])).

tff(c_35440,plain,
    ( k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') = k2_struct_0('#skF_5')
    | k3_xboole_0(k2_struct_0('#skF_5'),'#skF_7') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35289,c_35076])).

tff(c_35483,plain,(
    k3_xboole_0(k2_struct_0('#skF_5'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_35480,c_35440])).

tff(c_58840,plain,(
    k3_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58829,c_35483])).

tff(c_58857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35108,c_58840])).

tff(c_58859,plain,(
    k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_35443])).

tff(c_35228,plain,(
    ! [A_2190,B_2191] :
      ( k3_subset_1(A_2190,k3_subset_1(A_2190,B_2191)) = B_2191
      | ~ m1_subset_1(B_2191,k1_zfmisc_1(A_2190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35237,plain,(
    k3_subset_1(k2_struct_0('#skF_5'),k3_subset_1(k2_struct_0('#skF_5'),'#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_35068,c_35228])).

tff(c_58869,plain,(
    k3_subset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58859,c_35237])).

tff(c_35240,plain,(
    ! [A_20] : k3_subset_1(A_20,k3_subset_1(A_20,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_35228])).

tff(c_35294,plain,(
    ! [A_20] : k3_subset_1(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35293,c_35240])).

tff(c_58897,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_58869,c_35294])).

tff(c_58903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35045,c_58897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.69/11.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.95/11.38  
% 20.95/11.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.95/11.38  %$ v4_pre_topc > v3_pre_topc > v1_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 20.95/11.38  
% 20.95/11.38  %Foreground sorts:
% 20.95/11.38  
% 20.95/11.38  
% 20.95/11.38  %Background operators:
% 20.95/11.38  
% 20.95/11.38  
% 20.95/11.38  %Foreground operators:
% 20.95/11.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.95/11.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 20.95/11.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.95/11.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.95/11.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.95/11.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.95/11.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.95/11.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 20.95/11.38  tff('#skF_7', type, '#skF_7': $i).
% 20.95/11.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.95/11.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.95/11.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 20.95/11.38  tff('#skF_5', type, '#skF_5': $i).
% 20.95/11.38  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 20.95/11.38  tff('#skF_6', type, '#skF_6': $i).
% 20.95/11.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.95/11.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.95/11.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.95/11.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 20.95/11.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.95/11.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.95/11.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.95/11.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.95/11.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.95/11.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.95/11.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 20.95/11.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.95/11.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 20.95/11.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 20.95/11.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 20.95/11.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.95/11.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.95/11.38  
% 21.15/11.44  tff(f_186, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(C = k1_xboole_0) & v3_pre_topc(C, A)) & r1_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tops_1)).
% 21.15/11.44  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 21.15/11.44  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 21.15/11.44  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 21.15/11.44  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 21.15/11.44  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 21.15/11.44  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 21.15/11.44  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 21.15/11.44  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 21.15/11.44  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 21.15/11.44  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 21.15/11.44  tff(f_165, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 21.15/11.44  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k2_pre_topc(A, B)) <=> (![D]: (r2_hidden(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(E, A) & r2_hidden(D, E)) & r1_xboole_0(B, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_pre_topc)).
% 21.15/11.44  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 21.15/11.44  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 21.15/11.44  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 21.15/11.44  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 21.15/11.44  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 21.15/11.44  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 21.15/11.44  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_pre_topc)).
% 21.15/11.44  tff(f_156, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 21.15/11.44  tff(c_98, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_106, plain, (k1_xboole_0!='#skF_7' | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_167, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_106])).
% 21.15/11.44  tff(c_68, plain, (![A_111]: (l1_struct_0(A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_103])).
% 21.15/11.44  tff(c_168, plain, (![A_159]: (u1_struct_0(A_159)=k2_struct_0(A_159) | ~l1_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.15/11.44  tff(c_174, plain, (![A_162]: (u1_struct_0(A_162)=k2_struct_0(A_162) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_68, c_168])).
% 21.15/11.44  tff(c_178, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_98, c_174])).
% 21.15/11.44  tff(c_96, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_179, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_96])).
% 21.15/11.44  tff(c_17868, plain, (![B_1182, A_1183]: (v1_tops_1(B_1182, A_1183) | k2_pre_topc(A_1183, B_1182)!=k2_struct_0(A_1183) | ~m1_subset_1(B_1182, k1_zfmisc_1(u1_struct_0(A_1183))) | ~l1_pre_topc(A_1183))), inference(cnfTransformation, [status(thm)], [f_150])).
% 21.15/11.44  tff(c_17871, plain, (![B_1182]: (v1_tops_1(B_1182, '#skF_5') | k2_pre_topc('#skF_5', B_1182)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1182, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_17868])).
% 21.15/11.44  tff(c_18120, plain, (![B_1207]: (v1_tops_1(B_1207, '#skF_5') | k2_pre_topc('#skF_5', B_1207)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1207, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_17871])).
% 21.15/11.44  tff(c_18123, plain, (v1_tops_1('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_179, c_18120])).
% 21.15/11.44  tff(c_18134, plain, (k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_167, c_18123])).
% 21.15/11.44  tff(c_18, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.15/11.44  tff(c_22, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.15/11.44  tff(c_121, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 21.15/11.44  tff(c_17826, plain, (![A_1177, B_1178]: (k2_pre_topc(A_1177, B_1178)=B_1178 | ~v4_pre_topc(B_1178, A_1177) | ~m1_subset_1(B_1178, k1_zfmisc_1(u1_struct_0(A_1177))) | ~l1_pre_topc(A_1177))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.15/11.44  tff(c_17846, plain, (![A_1180]: (k2_pre_topc(A_1180, u1_struct_0(A_1180))=u1_struct_0(A_1180) | ~v4_pre_topc(u1_struct_0(A_1180), A_1180) | ~l1_pre_topc(A_1180))), inference(resolution, [status(thm)], [c_121, c_17826])).
% 21.15/11.44  tff(c_17849, plain, (k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))=u1_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_178, c_17846])).
% 21.15/11.44  tff(c_17851, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_178, c_178, c_17849])).
% 21.15/11.44  tff(c_17852, plain, (~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_17851])).
% 21.15/11.44  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.15/11.44  tff(c_28, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.15/11.44  tff(c_390, plain, (![A_192, B_193]: (k4_xboole_0(A_192, B_193)=k3_subset_1(A_192, B_193) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.15/11.44  tff(c_399, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k3_subset_1(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_390])).
% 21.15/11.44  tff(c_403, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_399])).
% 21.15/11.44  tff(c_314, plain, (![A_187, B_188]: (k3_subset_1(A_187, k3_subset_1(A_187, B_188))=B_188 | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.15/11.44  tff(c_323, plain, (![A_20]: (k3_subset_1(A_20, k3_subset_1(A_20, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_314])).
% 21.15/11.44  tff(c_404, plain, (![A_20]: (k3_subset_1(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_403, c_323])).
% 21.15/11.44  tff(c_18217, plain, (![B_1214, A_1215]: (v4_pre_topc(B_1214, A_1215) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1215), B_1214), A_1215) | ~m1_subset_1(B_1214, k1_zfmisc_1(u1_struct_0(A_1215))) | ~l1_pre_topc(A_1215))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_18221, plain, (![A_1215]: (v4_pre_topc(u1_struct_0(A_1215), A_1215) | ~v3_pre_topc(k1_xboole_0, A_1215) | ~m1_subset_1(u1_struct_0(A_1215), k1_zfmisc_1(u1_struct_0(A_1215))) | ~l1_pre_topc(A_1215))), inference(superposition, [status(thm), theory('equality')], [c_404, c_18217])).
% 21.15/11.44  tff(c_18257, plain, (![A_1218]: (v4_pre_topc(u1_struct_0(A_1218), A_1218) | ~v3_pre_topc(k1_xboole_0, A_1218) | ~l1_pre_topc(A_1218))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_18221])).
% 21.15/11.44  tff(c_18263, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_178, c_18257])).
% 21.15/11.44  tff(c_18266, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_18263])).
% 21.15/11.44  tff(c_18267, plain, (~v3_pre_topc(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_17852, c_18266])).
% 21.15/11.44  tff(c_18383, plain, (![A_1231, B_1232, C_1233]: (r2_hidden('#skF_2'(A_1231, B_1232, C_1233), u1_struct_0(A_1231)) | k2_pre_topc(A_1231, B_1232)=C_1233 | ~m1_subset_1(C_1233, k1_zfmisc_1(u1_struct_0(A_1231))) | ~m1_subset_1(B_1232, k1_zfmisc_1(u1_struct_0(A_1231))) | ~l1_pre_topc(A_1231))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_18394, plain, (![B_1232, C_1233]: (r2_hidden('#skF_2'('#skF_5', B_1232, C_1233), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1232)=C_1233 | ~m1_subset_1(C_1233, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_18383])).
% 21.15/11.44  tff(c_18399, plain, (![B_1232, C_1233]: (r2_hidden('#skF_2'('#skF_5', B_1232, C_1233), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1232)=C_1233 | ~m1_subset_1(C_1233, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_178, c_178, c_18394])).
% 21.15/11.44  tff(c_18915, plain, (![B_1317, A_1318, C_1319]: (r1_xboole_0(B_1317, '#skF_3'(A_1318, B_1317, C_1319)) | ~r2_hidden('#skF_2'(A_1318, B_1317, C_1319), C_1319) | k2_pre_topc(A_1318, B_1317)=C_1319 | ~m1_subset_1(C_1319, k1_zfmisc_1(u1_struct_0(A_1318))) | ~m1_subset_1(B_1317, k1_zfmisc_1(u1_struct_0(A_1318))) | ~l1_pre_topc(A_1318))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_18939, plain, (![B_1232]: (r1_xboole_0(B_1232, '#skF_3'('#skF_5', B_1232, k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1232)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_18399, c_18915])).
% 21.15/11.44  tff(c_18950, plain, (![B_1232]: (r1_xboole_0(B_1232, '#skF_3'('#skF_5', B_1232, k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_1232)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_18939])).
% 21.15/11.44  tff(c_18818, plain, (![A_1302, B_1303, C_1304]: (v3_pre_topc('#skF_3'(A_1302, B_1303, C_1304), A_1302) | ~r2_hidden('#skF_2'(A_1302, B_1303, C_1304), C_1304) | k2_pre_topc(A_1302, B_1303)=C_1304 | ~m1_subset_1(C_1304, k1_zfmisc_1(u1_struct_0(A_1302))) | ~m1_subset_1(B_1303, k1_zfmisc_1(u1_struct_0(A_1302))) | ~l1_pre_topc(A_1302))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_18839, plain, (![B_1232]: (v3_pre_topc('#skF_3'('#skF_5', B_1232, k2_struct_0('#skF_5')), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1232)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_18399, c_18818])).
% 21.15/11.44  tff(c_18849, plain, (![B_1232]: (v3_pre_topc('#skF_3'('#skF_5', B_1232, k2_struct_0('#skF_5')), '#skF_5') | k2_pre_topc('#skF_5', B_1232)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_18839])).
% 21.15/11.44  tff(c_19078, plain, (![A_1327, B_1328, C_1329]: (m1_subset_1('#skF_3'(A_1327, B_1328, C_1329), k1_zfmisc_1(u1_struct_0(A_1327))) | ~r2_hidden('#skF_2'(A_1327, B_1328, C_1329), C_1329) | k2_pre_topc(A_1327, B_1328)=C_1329 | ~m1_subset_1(C_1329, k1_zfmisc_1(u1_struct_0(A_1327))) | ~m1_subset_1(B_1328, k1_zfmisc_1(u1_struct_0(A_1327))) | ~l1_pre_topc(A_1327))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_19102, plain, (![B_1232]: (m1_subset_1('#skF_3'('#skF_5', B_1232, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1232)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1232, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_18399, c_19078])).
% 21.15/11.44  tff(c_19117, plain, (![B_1330]: (m1_subset_1('#skF_3'('#skF_5', B_1330, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_1330)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1330, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_178, c_19102])).
% 21.15/11.44  tff(c_120, plain, (![C_151]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_474, plain, (![C_151]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_120])).
% 21.15/11.44  tff(c_475, plain, (![C_151]: (~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_167, c_474])).
% 21.15/11.44  tff(c_19190, plain, (![B_1334]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_1334, k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_3'('#skF_5', B_1334, k2_struct_0('#skF_5')), '#skF_5') | '#skF_3'('#skF_5', B_1334, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_1334)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1334, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_19117, c_475])).
% 21.15/11.44  tff(c_27216, plain, (![B_1715]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_1715, k2_struct_0('#skF_5'))) | '#skF_3'('#skF_5', B_1715, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_1715)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1715, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_18849, c_19190])).
% 21.15/11.44  tff(c_27220, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18950, c_27216])).
% 21.15/11.44  tff(c_27229, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_27220])).
% 21.15/11.44  tff(c_27230, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18134, c_27229])).
% 21.15/11.44  tff(c_27266, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_27230, c_18849])).
% 21.15/11.44  tff(c_27297, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_27266])).
% 21.15/11.44  tff(c_27299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18134, c_18267, c_27297])).
% 21.15/11.44  tff(c_27301, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_17851])).
% 21.15/11.44  tff(c_27611, plain, (![A_1742, B_1743]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_1742), B_1743), A_1742) | ~v4_pre_topc(B_1743, A_1742) | ~m1_subset_1(B_1743, k1_zfmisc_1(u1_struct_0(A_1742))) | ~l1_pre_topc(A_1742))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_27615, plain, (![A_1742]: (v3_pre_topc(k1_xboole_0, A_1742) | ~v4_pre_topc(u1_struct_0(A_1742), A_1742) | ~m1_subset_1(u1_struct_0(A_1742), k1_zfmisc_1(u1_struct_0(A_1742))) | ~l1_pre_topc(A_1742))), inference(superposition, [status(thm), theory('equality')], [c_404, c_27611])).
% 21.15/11.44  tff(c_27629, plain, (![A_1744]: (v3_pre_topc(k1_xboole_0, A_1744) | ~v4_pre_topc(u1_struct_0(A_1744), A_1744) | ~l1_pre_topc(A_1744))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_27615])).
% 21.15/11.44  tff(c_27632, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_178, c_27629])).
% 21.15/11.44  tff(c_27634, plain, (v3_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_27301, c_27632])).
% 21.15/11.44  tff(c_27306, plain, (![B_1716, A_1717]: (v1_tops_1(B_1716, A_1717) | k2_pre_topc(A_1717, B_1716)!=k2_struct_0(A_1717) | ~m1_subset_1(B_1716, k1_zfmisc_1(u1_struct_0(A_1717))) | ~l1_pre_topc(A_1717))), inference(cnfTransformation, [status(thm)], [f_150])).
% 21.15/11.44  tff(c_27309, plain, (![B_1716]: (v1_tops_1(B_1716, '#skF_5') | k2_pre_topc('#skF_5', B_1716)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1716, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_27306])).
% 21.15/11.44  tff(c_27533, plain, (![B_1736]: (v1_tops_1(B_1736, '#skF_5') | k2_pre_topc('#skF_5', B_1736)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1736, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_27309])).
% 21.15/11.44  tff(c_27536, plain, (v1_tops_1('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_179, c_27533])).
% 21.15/11.44  tff(c_27547, plain, (k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_167, c_27536])).
% 21.15/11.44  tff(c_27821, plain, (![A_1762, B_1763, C_1764]: (r2_hidden('#skF_2'(A_1762, B_1763, C_1764), u1_struct_0(A_1762)) | k2_pre_topc(A_1762, B_1763)=C_1764 | ~m1_subset_1(C_1764, k1_zfmisc_1(u1_struct_0(A_1762))) | ~m1_subset_1(B_1763, k1_zfmisc_1(u1_struct_0(A_1762))) | ~l1_pre_topc(A_1762))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_27829, plain, (![B_1763, C_1764]: (r2_hidden('#skF_2'('#skF_5', B_1763, C_1764), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1763)=C_1764 | ~m1_subset_1(C_1764, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_27821])).
% 21.15/11.44  tff(c_27833, plain, (![B_1763, C_1764]: (r2_hidden('#skF_2'('#skF_5', B_1763, C_1764), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1763)=C_1764 | ~m1_subset_1(C_1764, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_178, c_178, c_27829])).
% 21.15/11.44  tff(c_28309, plain, (![B_1842, A_1843, C_1844]: (r1_xboole_0(B_1842, '#skF_3'(A_1843, B_1842, C_1844)) | ~r2_hidden('#skF_2'(A_1843, B_1842, C_1844), C_1844) | k2_pre_topc(A_1843, B_1842)=C_1844 | ~m1_subset_1(C_1844, k1_zfmisc_1(u1_struct_0(A_1843))) | ~m1_subset_1(B_1842, k1_zfmisc_1(u1_struct_0(A_1843))) | ~l1_pre_topc(A_1843))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_28330, plain, (![B_1763]: (r1_xboole_0(B_1763, '#skF_3'('#skF_5', B_1763, k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1763)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_27833, c_28309])).
% 21.15/11.44  tff(c_28341, plain, (![B_1763]: (r1_xboole_0(B_1763, '#skF_3'('#skF_5', B_1763, k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_1763)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_28330])).
% 21.15/11.44  tff(c_28221, plain, (![A_1827, B_1828, C_1829]: (v3_pre_topc('#skF_3'(A_1827, B_1828, C_1829), A_1827) | ~r2_hidden('#skF_2'(A_1827, B_1828, C_1829), C_1829) | k2_pre_topc(A_1827, B_1828)=C_1829 | ~m1_subset_1(C_1829, k1_zfmisc_1(u1_struct_0(A_1827))) | ~m1_subset_1(B_1828, k1_zfmisc_1(u1_struct_0(A_1827))) | ~l1_pre_topc(A_1827))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_28236, plain, (![B_1763]: (v3_pre_topc('#skF_3'('#skF_5', B_1763, k2_struct_0('#skF_5')), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1763)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_27833, c_28221])).
% 21.15/11.44  tff(c_28245, plain, (![B_1763]: (v3_pre_topc('#skF_3'('#skF_5', B_1763, k2_struct_0('#skF_5')), '#skF_5') | k2_pre_topc('#skF_5', B_1763)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_28236])).
% 21.15/11.44  tff(c_28445, plain, (![A_1856, B_1857, C_1858]: (m1_subset_1('#skF_3'(A_1856, B_1857, C_1858), k1_zfmisc_1(u1_struct_0(A_1856))) | ~r2_hidden('#skF_2'(A_1856, B_1857, C_1858), C_1858) | k2_pre_topc(A_1856, B_1857)=C_1858 | ~m1_subset_1(C_1858, k1_zfmisc_1(u1_struct_0(A_1856))) | ~m1_subset_1(B_1857, k1_zfmisc_1(u1_struct_0(A_1856))) | ~l1_pre_topc(A_1856))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_28466, plain, (![B_1763]: (m1_subset_1('#skF_3'('#skF_5', B_1763, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1763)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1763, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_27833, c_28445])).
% 21.15/11.44  tff(c_28518, plain, (![B_1865]: (m1_subset_1('#skF_3'('#skF_5', B_1865, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_1865)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1865, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_98, c_178, c_121, c_178, c_178, c_28466])).
% 21.15/11.44  tff(c_28860, plain, (![B_1896]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_1896, k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_3'('#skF_5', B_1896, k2_struct_0('#skF_5')), '#skF_5') | '#skF_3'('#skF_5', B_1896, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_1896)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1896, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_28518, c_475])).
% 21.15/11.44  tff(c_31287, plain, (![B_2047]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_2047, k2_struct_0('#skF_5'))) | '#skF_3'('#skF_5', B_2047, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_2047)=k2_struct_0('#skF_5') | ~m1_subset_1(B_2047, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_28245, c_28860])).
% 21.15/11.44  tff(c_31291, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_28341, c_31287])).
% 21.15/11.44  tff(c_31300, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_31291])).
% 21.15/11.44  tff(c_31301, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_27547, c_31300])).
% 21.15/11.44  tff(c_38, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), '#skF_3'(A_26, B_70, C_92)) | ~r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_31317, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_31301, c_38])).
% 21.15/11.44  tff(c_31336, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_179, c_178, c_121, c_178, c_31317])).
% 21.15/11.44  tff(c_31337, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_27547, c_31336])).
% 21.15/11.44  tff(c_31368, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_31337])).
% 21.15/11.44  tff(c_31377, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_27833, c_31368])).
% 21.15/11.44  tff(c_31382, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_121, c_31377])).
% 21.15/11.44  tff(c_31384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27547, c_31382])).
% 21.15/11.44  tff(c_31385, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_31337])).
% 21.15/11.44  tff(c_302, plain, (![A_180, C_181, B_182]: (m1_subset_1(A_180, C_181) | ~m1_subset_1(B_182, k1_zfmisc_1(C_181)) | ~r2_hidden(A_180, B_182))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.15/11.44  tff(c_311, plain, (![A_180, A_20]: (m1_subset_1(A_180, A_20) | ~r2_hidden(A_180, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_302])).
% 21.15/11.44  tff(c_31552, plain, (![A_2053]: (m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_2053))), inference(resolution, [status(thm)], [c_31385, c_311])).
% 21.15/11.44  tff(c_20, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.15/11.44  tff(c_31736, plain, (![A_2060]: (k4_xboole_0(A_2060, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))=k3_subset_1(A_2060, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_31552, c_20])).
% 21.15/11.44  tff(c_12, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.15/11.44  tff(c_31759, plain, (k3_subset_1(k1_xboole_0, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31736, c_12])).
% 21.15/11.44  tff(c_24, plain, (![A_14, B_15]: (k3_subset_1(A_14, k3_subset_1(A_14, B_15))=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.15/11.44  tff(c_31916, plain, (![A_2067]: (k3_subset_1(A_2067, k3_subset_1(A_2067, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))='#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_31552, c_24])).
% 21.15/11.44  tff(c_31945, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k3_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_31759, c_31916])).
% 21.15/11.44  tff(c_31963, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_404, c_31945])).
% 21.15/11.44  tff(c_31670, plain, (![A_11]: (k4_xboole_0(A_11, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))=k3_subset_1(A_11, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_31552, c_20])).
% 21.15/11.44  tff(c_16, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.15/11.44  tff(c_31804, plain, (![A_2061]: (k3_subset_1(A_2061, k3_subset_1(A_2061, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))='#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_31552, c_24])).
% 21.15/11.44  tff(c_31833, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k3_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_31759, c_31804])).
% 21.15/11.44  tff(c_31849, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_404, c_31833])).
% 21.15/11.44  tff(c_31669, plain, (~r1_xboole_0('#skF_6', '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), '#skF_5') | '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_31552, c_475])).
% 21.15/11.44  tff(c_31803, plain, (~v3_pre_topc('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_31669])).
% 21.15/11.44  tff(c_31855, plain, (~v3_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31803])).
% 21.15/11.44  tff(c_31864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27634, c_31855])).
% 21.15/11.44  tff(c_31865, plain, (~r1_xboole_0('#skF_6', '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))) | '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_31669])).
% 21.15/11.44  tff(c_31867, plain, (~r1_xboole_0('#skF_6', '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_31865])).
% 21.15/11.44  tff(c_31878, plain, (k4_xboole_0('#skF_6', '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))!='#skF_6'), inference(resolution, [status(thm)], [c_16, c_31867])).
% 21.15/11.44  tff(c_31883, plain, (k3_subset_1('#skF_6', '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_31670, c_31878])).
% 21.15/11.44  tff(c_31969, plain, (k3_subset_1('#skF_6', k1_xboole_0)!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_31963, c_31883])).
% 21.15/11.44  tff(c_31981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_403, c_31969])).
% 21.15/11.44  tff(c_31982, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_31865])).
% 21.15/11.44  tff(c_31447, plain, (![A_20]: (m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_20))), inference(resolution, [status(thm)], [c_31385, c_311])).
% 21.15/11.44  tff(c_31988, plain, (![A_20]: (m1_subset_1(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_31982, c_31447])).
% 21.15/11.44  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.15/11.44  tff(c_26, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 21.15/11.44  tff(c_31417, plain, (![A_16]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_16) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_31385, c_26])).
% 21.15/11.44  tff(c_31446, plain, (![A_16]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_31417])).
% 21.15/11.44  tff(c_31989, plain, (![A_16]: (r2_hidden(k1_xboole_0, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_31982, c_31446])).
% 21.15/11.44  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.15/11.44  tff(c_28603, plain, (![B_1871, D_1872, C_1873, A_1874]: (~r1_xboole_0(B_1871, D_1872) | ~r2_hidden(C_1873, D_1872) | ~v3_pre_topc(D_1872, A_1874) | ~m1_subset_1(D_1872, k1_zfmisc_1(u1_struct_0(A_1874))) | ~r2_hidden(C_1873, k2_pre_topc(A_1874, B_1871)) | ~m1_subset_1(C_1873, u1_struct_0(A_1874)) | ~m1_subset_1(B_1871, k1_zfmisc_1(u1_struct_0(A_1874))) | ~l1_pre_topc(A_1874))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_32389, plain, (![C_2084, B_2085, A_2086, A_2087]: (~r2_hidden(C_2084, B_2085) | ~v3_pre_topc(B_2085, A_2086) | ~m1_subset_1(B_2085, k1_zfmisc_1(u1_struct_0(A_2086))) | ~r2_hidden(C_2084, k2_pre_topc(A_2086, A_2087)) | ~m1_subset_1(C_2084, u1_struct_0(A_2086)) | ~m1_subset_1(A_2087, k1_zfmisc_1(u1_struct_0(A_2086))) | ~l1_pre_topc(A_2086) | k3_xboole_0(A_2087, B_2085)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_28603])).
% 21.15/11.44  tff(c_32391, plain, (![A_16, A_2086, A_2087]: (~v3_pre_topc(A_16, A_2086) | ~m1_subset_1(A_16, k1_zfmisc_1(u1_struct_0(A_2086))) | ~r2_hidden(k1_xboole_0, k2_pre_topc(A_2086, A_2087)) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_2086)) | ~m1_subset_1(A_2087, k1_zfmisc_1(u1_struct_0(A_2086))) | ~l1_pre_topc(A_2086) | k3_xboole_0(A_2087, A_16)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_31989, c_32389])).
% 21.15/11.44  tff(c_34964, plain, (![A_2160, A_2161, A_2162]: (~v3_pre_topc(A_2160, A_2161) | ~m1_subset_1(A_2160, k1_zfmisc_1(u1_struct_0(A_2161))) | ~m1_subset_1(A_2162, k1_zfmisc_1(u1_struct_0(A_2161))) | ~l1_pre_topc(A_2161) | k3_xboole_0(A_2162, A_2160)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31988, c_31989, c_32391])).
% 21.15/11.44  tff(c_34969, plain, (![A_2161, A_2162]: (~v3_pre_topc(k1_xboole_0, A_2161) | ~m1_subset_1(A_2162, k1_zfmisc_1(u1_struct_0(A_2161))) | ~l1_pre_topc(A_2161) | k3_xboole_0(A_2162, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_31988, c_34964])).
% 21.15/11.44  tff(c_34999, plain, (![A_2163, A_2164]: (~v3_pre_topc(k1_xboole_0, A_2163) | ~m1_subset_1(A_2164, k1_zfmisc_1(u1_struct_0(A_2163))) | ~l1_pre_topc(A_2163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34969])).
% 21.15/11.44  tff(c_35037, plain, (![A_2165]: (~v3_pre_topc(k1_xboole_0, A_2165) | ~l1_pre_topc(A_2165))), inference(resolution, [status(thm)], [c_31988, c_34999])).
% 21.15/11.44  tff(c_35040, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_27634, c_35037])).
% 21.15/11.44  tff(c_35044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_35040])).
% 21.15/11.44  tff(c_35045, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_106])).
% 21.15/11.44  tff(c_35046, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_106])).
% 21.15/11.44  tff(c_102, plain, (r1_xboole_0('#skF_6', '#skF_7') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_35050, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_102])).
% 21.15/11.44  tff(c_35096, plain, (![A_2176, B_2177]: (k3_xboole_0(A_2176, B_2177)=k1_xboole_0 | ~r1_xboole_0(A_2176, B_2177))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.15/11.44  tff(c_35108, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_35050, c_35096])).
% 21.15/11.44  tff(c_35051, plain, (![A_2166]: (u1_struct_0(A_2166)=k2_struct_0(A_2166) | ~l1_struct_0(A_2166))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.15/11.44  tff(c_35057, plain, (![A_2169]: (u1_struct_0(A_2169)=k2_struct_0(A_2169) | ~l1_pre_topc(A_2169))), inference(resolution, [status(thm)], [c_68, c_35051])).
% 21.15/11.44  tff(c_35061, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_98, c_35057])).
% 21.15/11.44  tff(c_35062, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35061, c_96])).
% 21.15/11.44  tff(c_35450, plain, (![A_2210, B_2211]: (k2_pre_topc(A_2210, B_2211)=B_2211 | ~v4_pre_topc(B_2211, A_2210) | ~m1_subset_1(B_2211, k1_zfmisc_1(u1_struct_0(A_2210))) | ~l1_pre_topc(A_2210))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.15/11.44  tff(c_35453, plain, (![B_2211]: (k2_pre_topc('#skF_5', B_2211)=B_2211 | ~v4_pre_topc(B_2211, '#skF_5') | ~m1_subset_1(B_2211, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35450])).
% 21.15/11.44  tff(c_45921, plain, (![B_3016]: (k2_pre_topc('#skF_5', B_3016)=B_3016 | ~v4_pre_topc(B_3016, '#skF_5') | ~m1_subset_1(B_3016, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35453])).
% 21.15/11.44  tff(c_45937, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_45921])).
% 21.15/11.44  tff(c_52170, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_45937])).
% 21.15/11.44  tff(c_108, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_35068, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_35061, c_108])).
% 21.15/11.44  tff(c_45936, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_35068, c_45921])).
% 21.15/11.44  tff(c_45941, plain, (~v4_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_45936])).
% 21.15/11.44  tff(c_100, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_46176, plain, (![B_3032, A_3033]: (v4_pre_topc(B_3032, A_3033) | k2_pre_topc(A_3033, B_3032)!=B_3032 | ~v2_pre_topc(A_3033) | ~m1_subset_1(B_3032, k1_zfmisc_1(u1_struct_0(A_3033))) | ~l1_pre_topc(A_3033))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.15/11.44  tff(c_46179, plain, (![B_3032]: (v4_pre_topc(B_3032, '#skF_5') | k2_pre_topc('#skF_5', B_3032)!=B_3032 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_3032, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_46176])).
% 21.15/11.44  tff(c_46198, plain, (![B_3035]: (v4_pre_topc(B_3035, '#skF_5') | k2_pre_topc('#skF_5', B_3035)!=B_3035 | ~m1_subset_1(B_3035, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_100, c_46179])).
% 21.15/11.44  tff(c_46201, plain, (v4_pre_topc('#skF_7', '#skF_5') | k2_pre_topc('#skF_5', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_35068, c_46198])).
% 21.15/11.44  tff(c_46215, plain, (k2_pre_topc('#skF_5', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_45941, c_46201])).
% 21.15/11.44  tff(c_51854, plain, (![A_3399, B_3400, C_3401]: (r2_hidden('#skF_2'(A_3399, B_3400, C_3401), u1_struct_0(A_3399)) | k2_pre_topc(A_3399, B_3400)=C_3401 | ~m1_subset_1(C_3401, k1_zfmisc_1(u1_struct_0(A_3399))) | ~m1_subset_1(B_3400, k1_zfmisc_1(u1_struct_0(A_3399))) | ~l1_pre_topc(A_3399))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_51862, plain, (![B_3400, C_3401]: (r2_hidden('#skF_2'('#skF_5', B_3400, C_3401), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3400)=C_3401 | ~m1_subset_1(C_3401, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3400, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_51854])).
% 21.15/11.44  tff(c_51905, plain, (![B_3405, C_3406]: (r2_hidden('#skF_2'('#skF_5', B_3405, C_3406), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3405)=C_3406 | ~m1_subset_1(C_3406, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3405, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_51862])).
% 21.15/11.44  tff(c_35364, plain, (![A_2199, C_2200, B_2201]: (m1_subset_1(A_2199, C_2200) | ~m1_subset_1(B_2201, k1_zfmisc_1(C_2200)) | ~r2_hidden(A_2199, B_2201))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.15/11.44  tff(c_35375, plain, (![A_2199, A_13]: (m1_subset_1(A_2199, A_13) | ~r2_hidden(A_2199, A_13))), inference(resolution, [status(thm)], [c_121, c_35364])).
% 21.15/11.44  tff(c_51915, plain, (![B_3405, C_3406]: (m1_subset_1('#skF_2'('#skF_5', B_3405, C_3406), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3405)=C_3406 | ~m1_subset_1(C_3406, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3405, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_51905, c_35375])).
% 21.15/11.44  tff(c_90, plain, (![A_140]: (v3_pre_topc(k2_struct_0(A_140), A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_156])).
% 21.15/11.44  tff(c_45940, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_28, c_45921])).
% 21.15/11.44  tff(c_45942, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_35276, plain, (![A_2194, B_2195]: (k4_xboole_0(A_2194, B_2195)=k3_subset_1(A_2194, B_2195) | ~m1_subset_1(B_2195, k1_zfmisc_1(A_2194)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.15/11.44  tff(c_35288, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k3_subset_1(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_35276])).
% 21.15/11.44  tff(c_35293, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_35288])).
% 21.15/11.44  tff(c_46083, plain, (![B_3026, A_3027]: (v4_pre_topc(B_3026, A_3027) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_3027), B_3026), A_3027) | ~m1_subset_1(B_3026, k1_zfmisc_1(u1_struct_0(A_3027))) | ~l1_pre_topc(A_3027))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_46094, plain, (![A_3027]: (v4_pre_topc(k1_xboole_0, A_3027) | ~v3_pre_topc(u1_struct_0(A_3027), A_3027) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_3027))) | ~l1_pre_topc(A_3027))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_46083])).
% 21.15/11.44  tff(c_46145, plain, (![A_3031]: (v4_pre_topc(k1_xboole_0, A_3031) | ~v3_pre_topc(u1_struct_0(A_3031), A_3031) | ~l1_pre_topc(A_3031))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_46094])).
% 21.15/11.44  tff(c_46151, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_46145])).
% 21.15/11.44  tff(c_46154, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_46151])).
% 21.15/11.44  tff(c_46155, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_45942, c_46154])).
% 21.15/11.44  tff(c_46158, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_90, c_46155])).
% 21.15/11.44  tff(c_46162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_46158])).
% 21.15/11.44  tff(c_46163, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_46164, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_46310, plain, (![A_3042, B_3043]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_3042), B_3043), A_3042) | ~v4_pre_topc(B_3043, A_3042) | ~m1_subset_1(B_3043, k1_zfmisc_1(u1_struct_0(A_3042))) | ~l1_pre_topc(A_3042))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_46321, plain, (![A_3042]: (v3_pre_topc(u1_struct_0(A_3042), A_3042) | ~v4_pre_topc(k1_xboole_0, A_3042) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_3042))) | ~l1_pre_topc(A_3042))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_46310])).
% 21.15/11.44  tff(c_46342, plain, (![A_3045]: (v3_pre_topc(u1_struct_0(A_3045), A_3045) | ~v4_pre_topc(k1_xboole_0, A_3045) | ~l1_pre_topc(A_3045))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_46321])).
% 21.15/11.44  tff(c_46348, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_46342])).
% 21.15/11.44  tff(c_46351, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_46164, c_46348])).
% 21.15/11.44  tff(c_46474, plain, (![A_3056, B_3057, C_3058]: (r2_hidden('#skF_2'(A_3056, B_3057, C_3058), u1_struct_0(A_3056)) | k2_pre_topc(A_3056, B_3057)=C_3058 | ~m1_subset_1(C_3058, k1_zfmisc_1(u1_struct_0(A_3056))) | ~m1_subset_1(B_3057, k1_zfmisc_1(u1_struct_0(A_3056))) | ~l1_pre_topc(A_3056))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_46485, plain, (![B_3057, C_3058]: (r2_hidden('#skF_2'('#skF_5', B_3057, C_3058), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3057)=C_3058 | ~m1_subset_1(C_3058, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_46474])).
% 21.15/11.44  tff(c_46490, plain, (![B_3057, C_3058]: (r2_hidden('#skF_2'('#skF_5', B_3057, C_3058), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3057)=C_3058 | ~m1_subset_1(C_3058, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_46485])).
% 21.15/11.44  tff(c_49114, plain, (![A_3279, B_3280, C_3281, E_3282]: (v3_pre_topc('#skF_3'(A_3279, B_3280, C_3281), A_3279) | ~r1_xboole_0(B_3280, E_3282) | ~r2_hidden('#skF_2'(A_3279, B_3280, C_3281), E_3282) | ~v3_pre_topc(E_3282, A_3279) | ~m1_subset_1(E_3282, k1_zfmisc_1(u1_struct_0(A_3279))) | k2_pre_topc(A_3279, B_3280)=C_3281 | ~m1_subset_1(C_3281, k1_zfmisc_1(u1_struct_0(A_3279))) | ~m1_subset_1(B_3280, k1_zfmisc_1(u1_struct_0(A_3279))) | ~l1_pre_topc(A_3279))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_49160, plain, (![B_3057, C_3058]: (v3_pre_topc('#skF_3'('#skF_5', B_3057, C_3058), '#skF_5') | ~r1_xboole_0(B_3057, k2_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_3058, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_3057)=C_3058 | ~m1_subset_1(C_3058, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_46490, c_49114])).
% 21.15/11.44  tff(c_50479, plain, (![B_3357, C_3358]: (v3_pre_topc('#skF_3'('#skF_5', B_3357, C_3358), '#skF_5') | ~r1_xboole_0(B_3357, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3357)=C_3358 | ~m1_subset_1(C_3358, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3357, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_121, c_35061, c_46351, c_49160])).
% 21.15/11.44  tff(c_50512, plain, (![B_3359]: (v3_pre_topc('#skF_3'('#skF_5', B_3359, '#skF_7'), '#skF_5') | ~r1_xboole_0(B_3359, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3359)='#skF_7' | ~m1_subset_1(B_3359, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_50479])).
% 21.15/11.44  tff(c_50546, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_50512])).
% 21.15/11.44  tff(c_50560, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_46163, c_50546])).
% 21.15/11.44  tff(c_50561, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_35045, c_50560])).
% 21.15/11.44  tff(c_50562, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_50561])).
% 21.15/11.44  tff(c_50565, plain, (k4_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_50562])).
% 21.15/11.44  tff(c_50572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_50565])).
% 21.15/11.44  tff(c_50574, plain, (r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_50561])).
% 21.15/11.44  tff(c_35373, plain, (![A_2199]: (m1_subset_1(A_2199, k2_struct_0('#skF_5')) | ~r2_hidden(A_2199, '#skF_7'))), inference(resolution, [status(thm)], [c_35068, c_35364])).
% 21.15/11.44  tff(c_46424, plain, (![A_3050, C_3051, B_3052]: (~v2_struct_0(A_3050) | ~r2_hidden(C_3051, k2_pre_topc(A_3050, B_3052)) | ~m1_subset_1(C_3051, u1_struct_0(A_3050)) | ~m1_subset_1(B_3052, k1_zfmisc_1(u1_struct_0(A_3050))) | ~l1_pre_topc(A_3050))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_46430, plain, (![C_3051]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3051, k1_xboole_0) | ~m1_subset_1(C_3051, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46163, c_46424])).
% 21.15/11.44  tff(c_46438, plain, (![C_3051]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3051, k1_xboole_0) | ~m1_subset_1(C_3051, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_35061, c_35061, c_46430])).
% 21.15/11.44  tff(c_46441, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_46438])).
% 21.15/11.44  tff(c_35484, plain, (![A_2213, B_2214]: (k2_pre_topc(A_2213, B_2214)=k2_struct_0(A_2213) | ~v1_tops_1(B_2214, A_2213) | ~m1_subset_1(B_2214, k1_zfmisc_1(u1_struct_0(A_2213))) | ~l1_pre_topc(A_2213))), inference(cnfTransformation, [status(thm)], [f_150])).
% 21.15/11.44  tff(c_35487, plain, (![B_2214]: (k2_pre_topc('#skF_5', B_2214)=k2_struct_0('#skF_5') | ~v1_tops_1(B_2214, '#skF_5') | ~m1_subset_1(B_2214, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35484])).
% 21.15/11.44  tff(c_46225, plain, (![B_3036]: (k2_pre_topc('#skF_5', B_3036)=k2_struct_0('#skF_5') | ~v1_tops_1(B_3036, '#skF_5') | ~m1_subset_1(B_3036, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_46231, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_46225])).
% 21.15/11.44  tff(c_46243, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_46231])).
% 21.15/11.44  tff(c_80, plain, (![A_115, B_127, C_133]: (m1_subset_1('#skF_4'(A_115, B_127, C_133), k1_zfmisc_1(u1_struct_0(A_115))) | r2_hidden(C_133, k2_pre_topc(A_115, B_127)) | v2_struct_0(A_115) | ~m1_subset_1(C_133, u1_struct_0(A_115)) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_46540, plain, (![C_3074, A_3075, B_3076]: (r2_hidden(C_3074, '#skF_4'(A_3075, B_3076, C_3074)) | r2_hidden(C_3074, k2_pre_topc(A_3075, B_3076)) | v2_struct_0(A_3075) | ~m1_subset_1(C_3074, u1_struct_0(A_3075)) | ~m1_subset_1(B_3076, k1_zfmisc_1(u1_struct_0(A_3075))) | ~l1_pre_topc(A_3075))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_46542, plain, (![C_3074, B_3076]: (r2_hidden(C_3074, '#skF_4'('#skF_5', B_3076, C_3074)) | r2_hidden(C_3074, k2_pre_topc('#skF_5', B_3076)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3074, u1_struct_0('#skF_5')) | ~m1_subset_1(B_3076, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_46540])).
% 21.15/11.44  tff(c_46550, plain, (![C_3074, B_3076]: (r2_hidden(C_3074, '#skF_4'('#skF_5', B_3076, C_3074)) | r2_hidden(C_3074, k2_pre_topc('#skF_5', B_3076)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3074, k2_struct_0('#skF_5')) | ~m1_subset_1(B_3076, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_46542])).
% 21.15/11.44  tff(c_46557, plain, (![C_3080, B_3081]: (r2_hidden(C_3080, '#skF_4'('#skF_5', B_3081, C_3080)) | r2_hidden(C_3080, k2_pre_topc('#skF_5', B_3081)) | ~m1_subset_1(C_3080, k2_struct_0('#skF_5')) | ~m1_subset_1(B_3081, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_46441, c_46550])).
% 21.15/11.44  tff(c_46561, plain, (![C_3080]: (r2_hidden(C_3080, '#skF_4'('#skF_5', '#skF_6', C_3080)) | r2_hidden(C_3080, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_3080, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_35062, c_46557])).
% 21.15/11.44  tff(c_46595, plain, (![C_3086]: (r2_hidden(C_3086, '#skF_4'('#skF_5', '#skF_6', C_3086)) | r2_hidden(C_3086, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3086, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46243, c_46561])).
% 21.15/11.44  tff(c_46752, plain, (![C_3105, A_3106]: (r2_hidden(C_3105, A_3106) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_3105), k1_zfmisc_1(A_3106)) | r2_hidden(C_3105, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3105, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_46595, c_26])).
% 21.15/11.44  tff(c_46756, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_46752])).
% 21.15/11.44  tff(c_46763, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_46243, c_35061, c_46756])).
% 21.15/11.44  tff(c_46764, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_46441, c_46763])).
% 21.15/11.44  tff(c_104, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 21.15/11.44  tff(c_35048, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_104])).
% 21.15/11.44  tff(c_47243, plain, (![B_3158, D_3159, C_3160, A_3161]: (~r1_xboole_0(B_3158, D_3159) | ~r2_hidden(C_3160, D_3159) | ~v3_pre_topc(D_3159, A_3161) | ~m1_subset_1(D_3159, k1_zfmisc_1(u1_struct_0(A_3161))) | ~r2_hidden(C_3160, k2_pre_topc(A_3161, B_3158)) | ~m1_subset_1(C_3160, u1_struct_0(A_3161)) | ~m1_subset_1(B_3158, k1_zfmisc_1(u1_struct_0(A_3161))) | ~l1_pre_topc(A_3161))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_47327, plain, (![C_3166, A_3167]: (~r2_hidden(C_3166, '#skF_7') | ~v3_pre_topc('#skF_7', A_3167) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_3167))) | ~r2_hidden(C_3166, k2_pre_topc(A_3167, '#skF_6')) | ~m1_subset_1(C_3166, u1_struct_0(A_3167)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_3167))) | ~l1_pre_topc(A_3167))), inference(resolution, [status(thm)], [c_35050, c_47243])).
% 21.15/11.44  tff(c_47329, plain, (![C_3166]: (~r2_hidden(C_3166, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_3166, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_3166, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_47327])).
% 21.15/11.44  tff(c_47332, plain, (![C_3168]: (~r2_hidden(C_3168, '#skF_7') | ~r2_hidden(C_3168, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3168, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_46243, c_35068, c_35048, c_47329])).
% 21.15/11.44  tff(c_47341, plain, (![C_3169]: (~r2_hidden(C_3169, '#skF_7') | ~m1_subset_1(C_3169, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_46764, c_47332])).
% 21.15/11.44  tff(c_47352, plain, (![A_2199]: (~r2_hidden(A_2199, '#skF_7'))), inference(resolution, [status(thm)], [c_35373, c_47341])).
% 21.15/11.44  tff(c_48924, plain, (![A_3271, B_3272, C_3273, E_3274]: (r2_hidden('#skF_2'(A_3271, B_3272, C_3273), C_3273) | ~r1_xboole_0(B_3272, E_3274) | ~r2_hidden('#skF_2'(A_3271, B_3272, C_3273), E_3274) | ~v3_pre_topc(E_3274, A_3271) | ~m1_subset_1(E_3274, k1_zfmisc_1(u1_struct_0(A_3271))) | k2_pre_topc(A_3271, B_3272)=C_3273 | ~m1_subset_1(C_3273, k1_zfmisc_1(u1_struct_0(A_3271))) | ~m1_subset_1(B_3272, k1_zfmisc_1(u1_struct_0(A_3271))) | ~l1_pre_topc(A_3271))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_48970, plain, (![B_3057, C_3058]: (r2_hidden('#skF_2'('#skF_5', B_3057, C_3058), C_3058) | ~r1_xboole_0(B_3057, k2_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_3058, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_3057)=C_3058 | ~m1_subset_1(C_3058, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3057, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_46490, c_48924])).
% 21.15/11.44  tff(c_51189, plain, (![B_3384, C_3385]: (r2_hidden('#skF_2'('#skF_5', B_3384, C_3385), C_3385) | ~r1_xboole_0(B_3384, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3384)=C_3385 | ~m1_subset_1(C_3385, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3384, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_121, c_35061, c_46351, c_48970])).
% 21.15/11.44  tff(c_51204, plain, (![B_3384]: (r2_hidden('#skF_2'('#skF_5', B_3384, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_3384, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3384)='#skF_7' | ~m1_subset_1(B_3384, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_51189])).
% 21.15/11.44  tff(c_51778, plain, (![B_3394]: (~r1_xboole_0(B_3394, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3394)='#skF_7' | ~m1_subset_1(B_3394, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_47352, c_51204])).
% 21.15/11.44  tff(c_51819, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_51778])).
% 21.15/11.44  tff(c_51835, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_46163, c_50574, c_51819])).
% 21.15/11.44  tff(c_51837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35045, c_51835])).
% 21.15/11.44  tff(c_51839, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_46438])).
% 21.15/11.44  tff(c_35550, plain, (![B_2222]: (k2_pre_topc('#skF_5', B_2222)=B_2222 | ~v4_pre_topc(B_2222, '#skF_5') | ~m1_subset_1(B_2222, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35453])).
% 21.15/11.44  tff(c_35565, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_35068, c_35550])).
% 21.15/11.44  tff(c_35569, plain, (~v4_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_35565])).
% 21.15/11.44  tff(c_35571, plain, (![B_2223, A_2224]: (v4_pre_topc(B_2223, A_2224) | k2_pre_topc(A_2224, B_2223)!=B_2223 | ~v2_pre_topc(A_2224) | ~m1_subset_1(B_2223, k1_zfmisc_1(u1_struct_0(A_2224))) | ~l1_pre_topc(A_2224))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.15/11.44  tff(c_35574, plain, (![B_2223]: (v4_pre_topc(B_2223, '#skF_5') | k2_pre_topc('#skF_5', B_2223)!=B_2223 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_2223, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35571])).
% 21.15/11.44  tff(c_35825, plain, (![B_2241]: (v4_pre_topc(B_2241, '#skF_5') | k2_pre_topc('#skF_5', B_2241)!=B_2241 | ~m1_subset_1(B_2241, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_100, c_35574])).
% 21.15/11.44  tff(c_35828, plain, (v4_pre_topc('#skF_7', '#skF_5') | k2_pre_topc('#skF_5', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_35068, c_35825])).
% 21.15/11.44  tff(c_35842, plain, (k2_pre_topc('#skF_5', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_35569, c_35828])).
% 21.15/11.44  tff(c_40625, plain, (![A_2588, B_2589, C_2590]: (r2_hidden('#skF_2'(A_2588, B_2589, C_2590), u1_struct_0(A_2588)) | k2_pre_topc(A_2588, B_2589)=C_2590 | ~m1_subset_1(C_2590, k1_zfmisc_1(u1_struct_0(A_2588))) | ~m1_subset_1(B_2589, k1_zfmisc_1(u1_struct_0(A_2588))) | ~l1_pre_topc(A_2588))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_40633, plain, (![B_2589, C_2590]: (r2_hidden('#skF_2'('#skF_5', B_2589, C_2590), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2589)=C_2590 | ~m1_subset_1(C_2590, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_2589, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_40625])).
% 21.15/11.44  tff(c_40740, plain, (![B_2602, C_2603]: (r2_hidden('#skF_2'('#skF_5', B_2602, C_2603), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2602)=C_2603 | ~m1_subset_1(C_2603, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2602, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_40633])).
% 21.15/11.44  tff(c_40750, plain, (![B_2602, C_2603]: (m1_subset_1('#skF_2'('#skF_5', B_2602, C_2603), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2602)=C_2603 | ~m1_subset_1(C_2603, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2602, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_40740, c_35375])).
% 21.15/11.44  tff(c_35568, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_28, c_35550])).
% 21.15/11.44  tff(c_35587, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_35646, plain, (![B_2228, A_2229]: (v4_pre_topc(B_2228, A_2229) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_2229), B_2228), A_2229) | ~m1_subset_1(B_2228, k1_zfmisc_1(u1_struct_0(A_2229))) | ~l1_pre_topc(A_2229))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_35654, plain, (![A_2229]: (v4_pre_topc(k1_xboole_0, A_2229) | ~v3_pre_topc(u1_struct_0(A_2229), A_2229) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_2229))) | ~l1_pre_topc(A_2229))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_35646])).
% 21.15/11.44  tff(c_35735, plain, (![A_2234]: (v4_pre_topc(k1_xboole_0, A_2234) | ~v3_pre_topc(u1_struct_0(A_2234), A_2234) | ~l1_pre_topc(A_2234))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_35654])).
% 21.15/11.44  tff(c_35738, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35735])).
% 21.15/11.44  tff(c_35740, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35738])).
% 21.15/11.44  tff(c_35741, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_35587, c_35740])).
% 21.15/11.44  tff(c_35767, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_90, c_35741])).
% 21.15/11.44  tff(c_35771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_35767])).
% 21.15/11.44  tff(c_35772, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_35959, plain, (![A_2248, C_2249, B_2250]: (~v2_struct_0(A_2248) | ~r2_hidden(C_2249, k2_pre_topc(A_2248, B_2250)) | ~m1_subset_1(C_2249, u1_struct_0(A_2248)) | ~m1_subset_1(B_2250, k1_zfmisc_1(u1_struct_0(A_2248))) | ~l1_pre_topc(A_2248))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_35965, plain, (![C_2249]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2249, k1_xboole_0) | ~m1_subset_1(C_2249, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35772, c_35959])).
% 21.15/11.44  tff(c_35971, plain, (![C_2249]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2249, k1_xboole_0) | ~m1_subset_1(C_2249, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_35061, c_35061, c_35965])).
% 21.15/11.44  tff(c_35983, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_35971])).
% 21.15/11.44  tff(c_35912, plain, (![B_2246]: (k2_pre_topc('#skF_5', B_2246)=k2_struct_0('#skF_5') | ~v1_tops_1(B_2246, '#skF_5') | ~m1_subset_1(B_2246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_35918, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_35912])).
% 21.15/11.44  tff(c_35932, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_35918])).
% 21.15/11.44  tff(c_36268, plain, (![C_2299, A_2300, B_2301]: (r2_hidden(C_2299, '#skF_4'(A_2300, B_2301, C_2299)) | r2_hidden(C_2299, k2_pre_topc(A_2300, B_2301)) | v2_struct_0(A_2300) | ~m1_subset_1(C_2299, u1_struct_0(A_2300)) | ~m1_subset_1(B_2301, k1_zfmisc_1(u1_struct_0(A_2300))) | ~l1_pre_topc(A_2300))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_36270, plain, (![C_2299, B_2301]: (r2_hidden(C_2299, '#skF_4'('#skF_5', B_2301, C_2299)) | r2_hidden(C_2299, k2_pre_topc('#skF_5', B_2301)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_2299, u1_struct_0('#skF_5')) | ~m1_subset_1(B_2301, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_36268])).
% 21.15/11.44  tff(c_36278, plain, (![C_2299, B_2301]: (r2_hidden(C_2299, '#skF_4'('#skF_5', B_2301, C_2299)) | r2_hidden(C_2299, k2_pre_topc('#skF_5', B_2301)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_2299, k2_struct_0('#skF_5')) | ~m1_subset_1(B_2301, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_36270])).
% 21.15/11.44  tff(c_36317, plain, (![C_2306, B_2307]: (r2_hidden(C_2306, '#skF_4'('#skF_5', B_2307, C_2306)) | r2_hidden(C_2306, k2_pre_topc('#skF_5', B_2307)) | ~m1_subset_1(C_2306, k2_struct_0('#skF_5')) | ~m1_subset_1(B_2307, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_35983, c_36278])).
% 21.15/11.44  tff(c_36321, plain, (![C_2306]: (r2_hidden(C_2306, '#skF_4'('#skF_5', '#skF_6', C_2306)) | r2_hidden(C_2306, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_2306, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_35062, c_36317])).
% 21.15/11.44  tff(c_36346, plain, (![C_2311]: (r2_hidden(C_2311, '#skF_4'('#skF_5', '#skF_6', C_2311)) | r2_hidden(C_2311, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2311, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35932, c_36321])).
% 21.15/11.44  tff(c_36814, plain, (![C_2355, A_2356]: (r2_hidden(C_2355, A_2356) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_2355), k1_zfmisc_1(A_2356)) | r2_hidden(C_2355, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2355, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36346, c_26])).
% 21.15/11.44  tff(c_36818, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_36814])).
% 21.15/11.44  tff(c_36825, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_35932, c_35061, c_36818])).
% 21.15/11.44  tff(c_36826, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_35983, c_36825])).
% 21.15/11.44  tff(c_36757, plain, (![B_2350, D_2351, C_2352, A_2353]: (~r1_xboole_0(B_2350, D_2351) | ~r2_hidden(C_2352, D_2351) | ~v3_pre_topc(D_2351, A_2353) | ~m1_subset_1(D_2351, k1_zfmisc_1(u1_struct_0(A_2353))) | ~r2_hidden(C_2352, k2_pre_topc(A_2353, B_2350)) | ~m1_subset_1(C_2352, u1_struct_0(A_2353)) | ~m1_subset_1(B_2350, k1_zfmisc_1(u1_struct_0(A_2353))) | ~l1_pre_topc(A_2353))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_36844, plain, (![C_2358, A_2359]: (~r2_hidden(C_2358, '#skF_7') | ~v3_pre_topc('#skF_7', A_2359) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_2359))) | ~r2_hidden(C_2358, k2_pre_topc(A_2359, '#skF_6')) | ~m1_subset_1(C_2358, u1_struct_0(A_2359)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2359))) | ~l1_pre_topc(A_2359))), inference(resolution, [status(thm)], [c_35050, c_36757])).
% 21.15/11.44  tff(c_36846, plain, (![C_2358]: (~r2_hidden(C_2358, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_2358, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_2358, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_36844])).
% 21.15/11.44  tff(c_36849, plain, (![C_2360]: (~r2_hidden(C_2360, '#skF_7') | ~r2_hidden(C_2360, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2360, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_35932, c_35068, c_35048, c_36846])).
% 21.15/11.44  tff(c_36858, plain, (![C_2361]: (~r2_hidden(C_2361, '#skF_7') | ~m1_subset_1(C_2361, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36826, c_36849])).
% 21.15/11.44  tff(c_36869, plain, (![A_2199]: (~r2_hidden(A_2199, '#skF_7'))), inference(resolution, [status(thm)], [c_35373, c_36858])).
% 21.15/11.44  tff(c_35773, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_35889, plain, (![A_2244, B_2245]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_2244), B_2245), A_2244) | ~v4_pre_topc(B_2245, A_2244) | ~m1_subset_1(B_2245, k1_zfmisc_1(u1_struct_0(A_2244))) | ~l1_pre_topc(A_2244))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_35900, plain, (![A_2244]: (v3_pre_topc(u1_struct_0(A_2244), A_2244) | ~v4_pre_topc(k1_xboole_0, A_2244) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_2244))) | ~l1_pre_topc(A_2244))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_35889])).
% 21.15/11.44  tff(c_35949, plain, (![A_2247]: (v3_pre_topc(u1_struct_0(A_2247), A_2247) | ~v4_pre_topc(k1_xboole_0, A_2247) | ~l1_pre_topc(A_2247))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_35900])).
% 21.15/11.44  tff(c_35955, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35949])).
% 21.15/11.44  tff(c_35958, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35773, c_35955])).
% 21.15/11.44  tff(c_34, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), u1_struct_0(A_26)) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_38674, plain, (![A_2486, B_2487, C_2488, E_2489]: (r2_hidden('#skF_2'(A_2486, B_2487, C_2488), C_2488) | ~r1_xboole_0(B_2487, E_2489) | ~r2_hidden('#skF_2'(A_2486, B_2487, C_2488), E_2489) | ~v3_pre_topc(E_2489, A_2486) | ~m1_subset_1(E_2489, k1_zfmisc_1(u1_struct_0(A_2486))) | k2_pre_topc(A_2486, B_2487)=C_2488 | ~m1_subset_1(C_2488, k1_zfmisc_1(u1_struct_0(A_2486))) | ~m1_subset_1(B_2487, k1_zfmisc_1(u1_struct_0(A_2486))) | ~l1_pre_topc(A_2486))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_38730, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_34, c_38674])).
% 21.15/11.44  tff(c_40223, plain, (![A_2576, B_2577, C_2578]: (r2_hidden('#skF_2'(A_2576, B_2577, C_2578), C_2578) | ~r1_xboole_0(B_2577, u1_struct_0(A_2576)) | ~v3_pre_topc(u1_struct_0(A_2576), A_2576) | k2_pre_topc(A_2576, B_2577)=C_2578 | ~m1_subset_1(C_2578, k1_zfmisc_1(u1_struct_0(A_2576))) | ~m1_subset_1(B_2577, k1_zfmisc_1(u1_struct_0(A_2576))) | ~l1_pre_topc(A_2576))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_38730])).
% 21.15/11.44  tff(c_40227, plain, (![B_2577, C_2578]: (r2_hidden('#skF_2'('#skF_5', B_2577, C_2578), C_2578) | ~r1_xboole_0(B_2577, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_2577)=C_2578 | ~m1_subset_1(C_2578, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_2577, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_40223])).
% 21.15/11.44  tff(c_40519, plain, (![B_2583, C_2584]: (r2_hidden('#skF_2'('#skF_5', B_2583, C_2584), C_2584) | ~r1_xboole_0(B_2583, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2583)=C_2584 | ~m1_subset_1(C_2584, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2583, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_35958, c_35061, c_40227])).
% 21.15/11.44  tff(c_40534, plain, (![B_2583]: (r2_hidden('#skF_2'('#skF_5', B_2583, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_2583, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2583)='#skF_7' | ~m1_subset_1(B_2583, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_40519])).
% 21.15/11.44  tff(c_40554, plain, (![B_2585]: (~r1_xboole_0(B_2585, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2585)='#skF_7' | ~m1_subset_1(B_2585, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_36869, c_40534])).
% 21.15/11.44  tff(c_40588, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_40554])).
% 21.15/11.44  tff(c_40601, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_35772, c_40588])).
% 21.15/11.44  tff(c_40602, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_35045, c_40601])).
% 21.15/11.44  tff(c_40605, plain, (k4_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_40602])).
% 21.15/11.44  tff(c_40612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_40605])).
% 21.15/11.44  tff(c_40614, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_35971])).
% 21.15/11.44  tff(c_35961, plain, (![C_2249]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2249, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2249, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35932, c_35959])).
% 21.15/11.44  tff(c_35967, plain, (![C_2249]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2249, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2249, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_35961])).
% 21.15/11.44  tff(c_40640, plain, (![C_2249]: (~r2_hidden(C_2249, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2249, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40614, c_35967])).
% 21.15/11.44  tff(c_40765, plain, (![B_2612, C_2613]: (~m1_subset_1('#skF_2'('#skF_5', B_2612, C_2613), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2612)=C_2613 | ~m1_subset_1(C_2613, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2612, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_40740, c_40640])).
% 21.15/11.44  tff(c_40791, plain, (![B_2617, C_2618]: (k2_pre_topc('#skF_5', B_2617)=C_2618 | ~m1_subset_1(C_2618, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2617, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_40750, c_40765])).
% 21.15/11.44  tff(c_40806, plain, (![B_2619]: (k2_pre_topc('#skF_5', B_2619)='#skF_7' | ~m1_subset_1(B_2619, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_40791])).
% 21.15/11.44  tff(c_40809, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_35068, c_40806])).
% 21.15/11.44  tff(c_40824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35842, c_40809])).
% 21.15/11.44  tff(c_40825, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_35565])).
% 21.15/11.44  tff(c_35518, plain, (![B_2218, A_2219]: (v1_tops_1(B_2218, A_2219) | k2_pre_topc(A_2219, B_2218)!=k2_struct_0(A_2219) | ~m1_subset_1(B_2218, k1_zfmisc_1(u1_struct_0(A_2219))) | ~l1_pre_topc(A_2219))), inference(cnfTransformation, [status(thm)], [f_150])).
% 21.15/11.44  tff(c_35521, plain, (![B_2218]: (v1_tops_1(B_2218, '#skF_5') | k2_pre_topc('#skF_5', B_2218)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_2218, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35518])).
% 21.15/11.44  tff(c_40992, plain, (![B_2629]: (v1_tops_1(B_2629, '#skF_5') | k2_pre_topc('#skF_5', B_2629)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_2629, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35521])).
% 21.15/11.44  tff(c_40995, plain, (v1_tops_1('#skF_7', '#skF_5') | k2_pre_topc('#skF_5', '#skF_7')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_35068, c_40992])).
% 21.15/11.44  tff(c_41008, plain, (v1_tops_1('#skF_7', '#skF_5') | k2_struct_0('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40825, c_40995])).
% 21.15/11.44  tff(c_41033, plain, (k2_struct_0('#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_41008])).
% 21.15/11.44  tff(c_45714, plain, (![A_2988, B_2989, C_2990]: (r2_hidden('#skF_2'(A_2988, B_2989, C_2990), u1_struct_0(A_2988)) | k2_pre_topc(A_2988, B_2989)=C_2990 | ~m1_subset_1(C_2990, k1_zfmisc_1(u1_struct_0(A_2988))) | ~m1_subset_1(B_2989, k1_zfmisc_1(u1_struct_0(A_2988))) | ~l1_pre_topc(A_2988))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_45722, plain, (![B_2989, C_2990]: (r2_hidden('#skF_2'('#skF_5', B_2989, C_2990), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2989)=C_2990 | ~m1_subset_1(C_2990, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_2989, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_45714])).
% 21.15/11.44  tff(c_45739, plain, (![B_2993, C_2994]: (r2_hidden('#skF_2'('#skF_5', B_2993, C_2994), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2993)=C_2994 | ~m1_subset_1(C_2994, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2993, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_45722])).
% 21.15/11.44  tff(c_45745, plain, (![B_2993, C_2994]: (m1_subset_1('#skF_2'('#skF_5', B_2993, C_2994), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2993)=C_2994 | ~m1_subset_1(C_2994, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2993, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_45739, c_35375])).
% 21.15/11.44  tff(c_45726, plain, (![B_2989, C_2990]: (r2_hidden('#skF_2'('#skF_5', B_2989, C_2990), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2989)=C_2990 | ~m1_subset_1(C_2990, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2989, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_45722])).
% 21.15/11.44  tff(c_40832, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_40856, plain, (![B_2621, A_2622]: (v4_pre_topc(B_2621, A_2622) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_2622), B_2621), A_2622) | ~m1_subset_1(B_2621, k1_zfmisc_1(u1_struct_0(A_2622))) | ~l1_pre_topc(A_2622))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_40864, plain, (![A_2622]: (v4_pre_topc(k1_xboole_0, A_2622) | ~v3_pre_topc(u1_struct_0(A_2622), A_2622) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_2622))) | ~l1_pre_topc(A_2622))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_40856])).
% 21.15/11.44  tff(c_40944, plain, (![A_2627]: (v4_pre_topc(k1_xboole_0, A_2627) | ~v3_pre_topc(u1_struct_0(A_2627), A_2627) | ~l1_pre_topc(A_2627))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40864])).
% 21.15/11.44  tff(c_40947, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_40944])).
% 21.15/11.44  tff(c_40949, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_40947])).
% 21.15/11.44  tff(c_40950, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40832, c_40949])).
% 21.15/11.44  tff(c_40974, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_90, c_40950])).
% 21.15/11.44  tff(c_40978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_40974])).
% 21.15/11.44  tff(c_40979, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_40980, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_35568])).
% 21.15/11.44  tff(c_41184, plain, (![A_2642, B_2643]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_2642), B_2643), A_2642) | ~v4_pre_topc(B_2643, A_2642) | ~m1_subset_1(B_2643, k1_zfmisc_1(u1_struct_0(A_2642))) | ~l1_pre_topc(A_2642))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_41195, plain, (![A_2642]: (v3_pre_topc(u1_struct_0(A_2642), A_2642) | ~v4_pre_topc(k1_xboole_0, A_2642) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_2642))) | ~l1_pre_topc(A_2642))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_41184])).
% 21.15/11.44  tff(c_41221, plain, (![A_2645]: (v3_pre_topc(u1_struct_0(A_2645), A_2645) | ~v4_pre_topc(k1_xboole_0, A_2645) | ~l1_pre_topc(A_2645))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_41195])).
% 21.15/11.44  tff(c_41227, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_41221])).
% 21.15/11.44  tff(c_41230, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_40980, c_41227])).
% 21.15/11.44  tff(c_43050, plain, (![A_2849, B_2850, C_2851, E_2852]: (v3_pre_topc('#skF_3'(A_2849, B_2850, C_2851), A_2849) | ~r1_xboole_0(B_2850, E_2852) | ~r2_hidden('#skF_2'(A_2849, B_2850, C_2851), E_2852) | ~v3_pre_topc(E_2852, A_2849) | ~m1_subset_1(E_2852, k1_zfmisc_1(u1_struct_0(A_2849))) | k2_pre_topc(A_2849, B_2850)=C_2851 | ~m1_subset_1(C_2851, k1_zfmisc_1(u1_struct_0(A_2849))) | ~m1_subset_1(B_2850, k1_zfmisc_1(u1_struct_0(A_2849))) | ~l1_pre_topc(A_2849))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_43090, plain, (![A_26, B_70, C_92]: (v3_pre_topc('#skF_3'(A_26, B_70, C_92), A_26) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_34, c_43050])).
% 21.15/11.44  tff(c_44985, plain, (![A_2955, B_2956, C_2957]: (v3_pre_topc('#skF_3'(A_2955, B_2956, C_2957), A_2955) | ~r1_xboole_0(B_2956, u1_struct_0(A_2955)) | ~v3_pre_topc(u1_struct_0(A_2955), A_2955) | k2_pre_topc(A_2955, B_2956)=C_2957 | ~m1_subset_1(C_2957, k1_zfmisc_1(u1_struct_0(A_2955))) | ~m1_subset_1(B_2956, k1_zfmisc_1(u1_struct_0(A_2955))) | ~l1_pre_topc(A_2955))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_43090])).
% 21.15/11.44  tff(c_44989, plain, (![B_2956, C_2957]: (v3_pre_topc('#skF_3'('#skF_5', B_2956, C_2957), '#skF_5') | ~r1_xboole_0(B_2956, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_2956)=C_2957 | ~m1_subset_1(C_2957, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_2956, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_44985])).
% 21.15/11.44  tff(c_45113, plain, (![B_2965, C_2966]: (v3_pre_topc('#skF_3'('#skF_5', B_2965, C_2966), '#skF_5') | ~r1_xboole_0(B_2965, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2965)=C_2966 | ~m1_subset_1(C_2966, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2965, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_41230, c_35061, c_44989])).
% 21.15/11.44  tff(c_45196, plain, (![B_2969]: (v3_pre_topc('#skF_3'('#skF_5', B_2969, '#skF_7'), '#skF_5') | ~r1_xboole_0(B_2969, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2969)='#skF_7' | ~m1_subset_1(B_2969, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_45113])).
% 21.15/11.44  tff(c_45229, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_45196])).
% 21.15/11.44  tff(c_45243, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40979, c_45229])).
% 21.15/11.44  tff(c_45244, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_35045, c_45243])).
% 21.15/11.44  tff(c_45245, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_45244])).
% 21.15/11.44  tff(c_45248, plain, (k4_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_45245])).
% 21.15/11.44  tff(c_45255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_45248])).
% 21.15/11.44  tff(c_45257, plain, (r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_45244])).
% 21.15/11.44  tff(c_41268, plain, (![A_2648, C_2649, B_2650]: (~v2_struct_0(A_2648) | ~r2_hidden(C_2649, k2_pre_topc(A_2648, B_2650)) | ~m1_subset_1(C_2649, u1_struct_0(A_2648)) | ~m1_subset_1(B_2650, k1_zfmisc_1(u1_struct_0(A_2648))) | ~l1_pre_topc(A_2648))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_41274, plain, (![C_2649]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2649, k1_xboole_0) | ~m1_subset_1(C_2649, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40979, c_41268])).
% 21.15/11.44  tff(c_41282, plain, (![C_2649]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2649, k1_xboole_0) | ~m1_subset_1(C_2649, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_35061, c_35061, c_41274])).
% 21.15/11.44  tff(c_41285, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_41282])).
% 21.15/11.44  tff(c_41035, plain, (![B_2632]: (k2_pre_topc('#skF_5', B_2632)=k2_struct_0('#skF_5') | ~v1_tops_1(B_2632, '#skF_5') | ~m1_subset_1(B_2632, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_41041, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_41035])).
% 21.15/11.44  tff(c_41055, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_41041])).
% 21.15/11.44  tff(c_41525, plain, (![C_2693, A_2694, B_2695]: (r2_hidden(C_2693, '#skF_4'(A_2694, B_2695, C_2693)) | r2_hidden(C_2693, k2_pre_topc(A_2694, B_2695)) | v2_struct_0(A_2694) | ~m1_subset_1(C_2693, u1_struct_0(A_2694)) | ~m1_subset_1(B_2695, k1_zfmisc_1(u1_struct_0(A_2694))) | ~l1_pre_topc(A_2694))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_41527, plain, (![C_2693, B_2695]: (r2_hidden(C_2693, '#skF_4'('#skF_5', B_2695, C_2693)) | r2_hidden(C_2693, k2_pre_topc('#skF_5', B_2695)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_2693, u1_struct_0('#skF_5')) | ~m1_subset_1(B_2695, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_41525])).
% 21.15/11.44  tff(c_41535, plain, (![C_2693, B_2695]: (r2_hidden(C_2693, '#skF_4'('#skF_5', B_2695, C_2693)) | r2_hidden(C_2693, k2_pre_topc('#skF_5', B_2695)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_2693, k2_struct_0('#skF_5')) | ~m1_subset_1(B_2695, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_41527])).
% 21.15/11.44  tff(c_41713, plain, (![C_2720, B_2721]: (r2_hidden(C_2720, '#skF_4'('#skF_5', B_2721, C_2720)) | r2_hidden(C_2720, k2_pre_topc('#skF_5', B_2721)) | ~m1_subset_1(C_2720, k2_struct_0('#skF_5')) | ~m1_subset_1(B_2721, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_41285, c_41535])).
% 21.15/11.44  tff(c_41717, plain, (![C_2720]: (r2_hidden(C_2720, '#skF_4'('#skF_5', '#skF_6', C_2720)) | r2_hidden(C_2720, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_2720, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_35062, c_41713])).
% 21.15/11.44  tff(c_41777, plain, (![C_2728]: (r2_hidden(C_2728, '#skF_4'('#skF_5', '#skF_6', C_2728)) | r2_hidden(C_2728, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2728, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_41055, c_41717])).
% 21.15/11.44  tff(c_42064, plain, (![C_2751, A_2752]: (r2_hidden(C_2751, A_2752) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_2751), k1_zfmisc_1(A_2752)) | r2_hidden(C_2751, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2751, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_41777, c_26])).
% 21.15/11.44  tff(c_42068, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_42064])).
% 21.15/11.44  tff(c_42075, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_41055, c_35061, c_42068])).
% 21.15/11.44  tff(c_42076, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_41285, c_42075])).
% 21.15/11.44  tff(c_42123, plain, (![B_2760, D_2761, C_2762, A_2763]: (~r1_xboole_0(B_2760, D_2761) | ~r2_hidden(C_2762, D_2761) | ~v3_pre_topc(D_2761, A_2763) | ~m1_subset_1(D_2761, k1_zfmisc_1(u1_struct_0(A_2763))) | ~r2_hidden(C_2762, k2_pre_topc(A_2763, B_2760)) | ~m1_subset_1(C_2762, u1_struct_0(A_2763)) | ~m1_subset_1(B_2760, k1_zfmisc_1(u1_struct_0(A_2763))) | ~l1_pre_topc(A_2763))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_42253, plain, (![C_2768, A_2769]: (~r2_hidden(C_2768, '#skF_7') | ~v3_pre_topc('#skF_7', A_2769) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_2769))) | ~r2_hidden(C_2768, k2_pre_topc(A_2769, '#skF_6')) | ~m1_subset_1(C_2768, u1_struct_0(A_2769)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2769))) | ~l1_pre_topc(A_2769))), inference(resolution, [status(thm)], [c_35050, c_42123])).
% 21.15/11.44  tff(c_42255, plain, (![C_2768]: (~r2_hidden(C_2768, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_2768, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_2768, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_42253])).
% 21.15/11.44  tff(c_42258, plain, (![C_2770]: (~r2_hidden(C_2770, '#skF_7') | ~r2_hidden(C_2770, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2770, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_41055, c_35068, c_35048, c_42255])).
% 21.15/11.44  tff(c_42267, plain, (![C_2771]: (~r2_hidden(C_2771, '#skF_7') | ~m1_subset_1(C_2771, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42076, c_42258])).
% 21.15/11.44  tff(c_42278, plain, (![A_2199]: (~r2_hidden(A_2199, '#skF_7'))), inference(resolution, [status(thm)], [c_35373, c_42267])).
% 21.15/11.44  tff(c_43308, plain, (![A_2869, B_2870, C_2871, E_2872]: (r2_hidden('#skF_2'(A_2869, B_2870, C_2871), C_2871) | ~r1_xboole_0(B_2870, E_2872) | ~r2_hidden('#skF_2'(A_2869, B_2870, C_2871), E_2872) | ~v3_pre_topc(E_2872, A_2869) | ~m1_subset_1(E_2872, k1_zfmisc_1(u1_struct_0(A_2869))) | k2_pre_topc(A_2869, B_2870)=C_2871 | ~m1_subset_1(C_2871, k1_zfmisc_1(u1_struct_0(A_2869))) | ~m1_subset_1(B_2870, k1_zfmisc_1(u1_struct_0(A_2869))) | ~l1_pre_topc(A_2869))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_43356, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_34, c_43308])).
% 21.15/11.44  tff(c_45278, plain, (![A_2970, B_2971, C_2972]: (r2_hidden('#skF_2'(A_2970, B_2971, C_2972), C_2972) | ~r1_xboole_0(B_2971, u1_struct_0(A_2970)) | ~v3_pre_topc(u1_struct_0(A_2970), A_2970) | k2_pre_topc(A_2970, B_2971)=C_2972 | ~m1_subset_1(C_2972, k1_zfmisc_1(u1_struct_0(A_2970))) | ~m1_subset_1(B_2971, k1_zfmisc_1(u1_struct_0(A_2970))) | ~l1_pre_topc(A_2970))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_43356])).
% 21.15/11.44  tff(c_45282, plain, (![B_2971, C_2972]: (r2_hidden('#skF_2'('#skF_5', B_2971, C_2972), C_2972) | ~r1_xboole_0(B_2971, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_2971)=C_2972 | ~m1_subset_1(C_2972, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_2971, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_45278])).
% 21.15/11.44  tff(c_45614, plain, (![B_2982, C_2983]: (r2_hidden('#skF_2'('#skF_5', B_2982, C_2983), C_2983) | ~r1_xboole_0(B_2982, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2982)=C_2983 | ~m1_subset_1(C_2983, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2982, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_41230, c_35061, c_45282])).
% 21.15/11.44  tff(c_45629, plain, (![B_2982]: (r2_hidden('#skF_2'('#skF_5', B_2982, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_2982, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2982)='#skF_7' | ~m1_subset_1(B_2982, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_45614])).
% 21.15/11.44  tff(c_45650, plain, (![B_2984]: (~r1_xboole_0(B_2984, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2984)='#skF_7' | ~m1_subset_1(B_2984, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_42278, c_45629])).
% 21.15/11.44  tff(c_45683, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_45650])).
% 21.15/11.44  tff(c_45698, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40979, c_45257, c_45683])).
% 21.15/11.44  tff(c_45700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35045, c_45698])).
% 21.15/11.44  tff(c_45702, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_41282])).
% 21.15/11.44  tff(c_41272, plain, (![C_2649]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2649, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2649, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_41055, c_41268])).
% 21.15/11.44  tff(c_41280, plain, (![C_2649]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_2649, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2649, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_41272])).
% 21.15/11.44  tff(c_45749, plain, (![C_2995]: (~r2_hidden(C_2995, k2_struct_0('#skF_5')) | ~m1_subset_1(C_2995, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_45702, c_41280])).
% 21.15/11.44  tff(c_45770, plain, (![B_3002, C_3003]: (~m1_subset_1('#skF_2'('#skF_5', B_3002, C_3003), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3002)=C_3003 | ~m1_subset_1(C_3003, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3002, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_45726, c_45749])).
% 21.15/11.44  tff(c_45792, plain, (![B_3007, C_3008]: (k2_pre_topc('#skF_5', B_3007)=C_3008 | ~m1_subset_1(C_3008, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3007, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_45745, c_45770])).
% 21.15/11.44  tff(c_45807, plain, (![B_3009]: (k2_pre_topc('#skF_5', B_3009)='#skF_7' | ~m1_subset_1(B_3009, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_45792])).
% 21.15/11.44  tff(c_45824, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_35062, c_45807])).
% 21.15/11.44  tff(c_45827, plain, (k2_struct_0('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_45824, c_41055])).
% 21.15/11.44  tff(c_45829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41033, c_45827])).
% 21.15/11.44  tff(c_45831, plain, (k2_struct_0('#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_41008])).
% 21.15/11.44  tff(c_35504, plain, (![A_2216]: (k2_pre_topc(A_2216, u1_struct_0(A_2216))=k2_struct_0(A_2216) | ~v1_tops_1(u1_struct_0(A_2216), A_2216) | ~l1_pre_topc(A_2216))), inference(resolution, [status(thm)], [c_121, c_35484])).
% 21.15/11.44  tff(c_35507, plain, (k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35504])).
% 21.15/11.44  tff(c_35509, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35507])).
% 21.15/11.44  tff(c_35510, plain, (~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_35509])).
% 21.15/11.44  tff(c_35539, plain, (![A_2221]: (v1_tops_1(u1_struct_0(A_2221), A_2221) | k2_pre_topc(A_2221, u1_struct_0(A_2221))!=k2_struct_0(A_2221) | ~l1_pre_topc(A_2221))), inference(resolution, [status(thm)], [c_121, c_35518])).
% 21.15/11.44  tff(c_35545, plain, (v1_tops_1(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))!=k2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_35539])).
% 21.15/11.44  tff(c_35548, plain, (v1_tops_1(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35545])).
% 21.15/11.44  tff(c_35549, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_35510, c_35548])).
% 21.15/11.44  tff(c_45858, plain, (k2_pre_topc('#skF_5', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_45831, c_45831, c_35549])).
% 21.15/11.44  tff(c_45877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40825, c_45858])).
% 21.15/11.44  tff(c_45878, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_35509])).
% 21.15/11.44  tff(c_46432, plain, (![C_3051]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3051, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3051, u1_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_45878, c_46424])).
% 21.15/11.44  tff(c_46440, plain, (![C_3051]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3051, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3051, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_121, c_35061, c_35061, c_46432])).
% 21.15/11.44  tff(c_51852, plain, (![C_3051]: (~r2_hidden(C_3051, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3051, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_51839, c_46440])).
% 21.15/11.44  tff(c_51942, plain, (![B_3416, C_3417]: (~m1_subset_1('#skF_2'('#skF_5', B_3416, C_3417), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3416)=C_3417 | ~m1_subset_1(C_3417, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3416, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_51905, c_51852])).
% 21.15/11.44  tff(c_51955, plain, (![B_3418, C_3419]: (k2_pre_topc('#skF_5', B_3418)=C_3419 | ~m1_subset_1(C_3419, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3418, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_51915, c_51942])).
% 21.15/11.44  tff(c_51970, plain, (![B_3420]: (k2_pre_topc('#skF_5', B_3420)='#skF_7' | ~m1_subset_1(B_3420, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_51955])).
% 21.15/11.44  tff(c_51973, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_35068, c_51970])).
% 21.15/11.44  tff(c_51988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46215, c_51973])).
% 21.15/11.44  tff(c_51989, plain, (k2_pre_topc('#skF_5', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_45936])).
% 21.15/11.44  tff(c_45890, plain, (![B_3012, A_3013]: (v1_tops_1(B_3012, A_3013) | k2_pre_topc(A_3013, B_3012)!=k2_struct_0(A_3013) | ~m1_subset_1(B_3012, k1_zfmisc_1(u1_struct_0(A_3013))) | ~l1_pre_topc(A_3013))), inference(cnfTransformation, [status(thm)], [f_150])).
% 21.15/11.44  tff(c_45893, plain, (![B_3012]: (v1_tops_1(B_3012, '#skF_5') | k2_pre_topc('#skF_5', B_3012)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_3012, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_45890])).
% 21.15/11.44  tff(c_52182, plain, (![B_3432]: (v1_tops_1(B_3432, '#skF_5') | k2_pre_topc('#skF_5', B_3432)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_3432, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_45893])).
% 21.15/11.44  tff(c_52185, plain, (v1_tops_1('#skF_7', '#skF_5') | k2_pre_topc('#skF_5', '#skF_7')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_35068, c_52182])).
% 21.15/11.44  tff(c_52198, plain, (v1_tops_1('#skF_7', '#skF_5') | k2_struct_0('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_51989, c_52185])).
% 21.15/11.44  tff(c_52224, plain, (k2_struct_0('#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_52198])).
% 21.15/11.44  tff(c_57181, plain, (![A_3814, B_3815, C_3816]: (r2_hidden('#skF_2'(A_3814, B_3815, C_3816), u1_struct_0(A_3814)) | k2_pre_topc(A_3814, B_3815)=C_3816 | ~m1_subset_1(C_3816, k1_zfmisc_1(u1_struct_0(A_3814))) | ~m1_subset_1(B_3815, k1_zfmisc_1(u1_struct_0(A_3814))) | ~l1_pre_topc(A_3814))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_57189, plain, (![B_3815, C_3816]: (r2_hidden('#skF_2'('#skF_5', B_3815, C_3816), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3815)=C_3816 | ~m1_subset_1(C_3816, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3815, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_57181])).
% 21.15/11.44  tff(c_57221, plain, (![B_3822, C_3823]: (r2_hidden('#skF_2'('#skF_5', B_3822, C_3823), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3822)=C_3823 | ~m1_subset_1(C_3823, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3822, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_57189])).
% 21.15/11.44  tff(c_57231, plain, (![B_3822, C_3823]: (m1_subset_1('#skF_2'('#skF_5', B_3822, C_3823), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3822)=C_3823 | ~m1_subset_1(C_3823, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3822, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_57221, c_35375])).
% 21.15/11.44  tff(c_51995, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_52075, plain, (![B_3426, A_3427]: (v4_pre_topc(B_3426, A_3427) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_3427), B_3426), A_3427) | ~m1_subset_1(B_3426, k1_zfmisc_1(u1_struct_0(A_3427))) | ~l1_pre_topc(A_3427))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_52083, plain, (![A_3427]: (v4_pre_topc(k1_xboole_0, A_3427) | ~v3_pre_topc(u1_struct_0(A_3427), A_3427) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_3427))) | ~l1_pre_topc(A_3427))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_52075])).
% 21.15/11.44  tff(c_52154, plain, (![A_3431]: (v4_pre_topc(k1_xboole_0, A_3431) | ~v3_pre_topc(u1_struct_0(A_3431), A_3431) | ~l1_pre_topc(A_3431))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_52083])).
% 21.15/11.44  tff(c_52157, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_52154])).
% 21.15/11.44  tff(c_52159, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_52157])).
% 21.15/11.44  tff(c_52160, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_51995, c_52159])).
% 21.15/11.44  tff(c_52163, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_90, c_52160])).
% 21.15/11.44  tff(c_52167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_52163])).
% 21.15/11.44  tff(c_52168, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_52169, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_45940])).
% 21.15/11.44  tff(c_52454, plain, (![A_3452, B_3453]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_3452), B_3453), A_3452) | ~v4_pre_topc(B_3453, A_3452) | ~m1_subset_1(B_3453, k1_zfmisc_1(u1_struct_0(A_3452))) | ~l1_pre_topc(A_3452))), inference(cnfTransformation, [status(thm)], [f_165])).
% 21.15/11.44  tff(c_52465, plain, (![A_3452]: (v3_pre_topc(u1_struct_0(A_3452), A_3452) | ~v4_pre_topc(k1_xboole_0, A_3452) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_3452))) | ~l1_pre_topc(A_3452))), inference(superposition, [status(thm), theory('equality')], [c_35293, c_52454])).
% 21.15/11.44  tff(c_52490, plain, (![A_3455]: (v3_pre_topc(u1_struct_0(A_3455), A_3455) | ~v4_pre_topc(k1_xboole_0, A_3455) | ~l1_pre_topc(A_3455))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_52465])).
% 21.15/11.44  tff(c_52496, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35061, c_52490])).
% 21.15/11.44  tff(c_52499, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_52169, c_52496])).
% 21.15/11.44  tff(c_54789, plain, (![A_3689, B_3690, C_3691, E_3692]: (v3_pre_topc('#skF_3'(A_3689, B_3690, C_3691), A_3689) | ~r1_xboole_0(B_3690, E_3692) | ~r2_hidden('#skF_2'(A_3689, B_3690, C_3691), E_3692) | ~v3_pre_topc(E_3692, A_3689) | ~m1_subset_1(E_3692, k1_zfmisc_1(u1_struct_0(A_3689))) | k2_pre_topc(A_3689, B_3690)=C_3691 | ~m1_subset_1(C_3691, k1_zfmisc_1(u1_struct_0(A_3689))) | ~m1_subset_1(B_3690, k1_zfmisc_1(u1_struct_0(A_3689))) | ~l1_pre_topc(A_3689))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_54829, plain, (![A_26, B_70, C_92]: (v3_pre_topc('#skF_3'(A_26, B_70, C_92), A_26) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_34, c_54789])).
% 21.15/11.44  tff(c_56248, plain, (![A_3768, B_3769, C_3770]: (v3_pre_topc('#skF_3'(A_3768, B_3769, C_3770), A_3768) | ~r1_xboole_0(B_3769, u1_struct_0(A_3768)) | ~v3_pre_topc(u1_struct_0(A_3768), A_3768) | k2_pre_topc(A_3768, B_3769)=C_3770 | ~m1_subset_1(C_3770, k1_zfmisc_1(u1_struct_0(A_3768))) | ~m1_subset_1(B_3769, k1_zfmisc_1(u1_struct_0(A_3768))) | ~l1_pre_topc(A_3768))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_54829])).
% 21.15/11.44  tff(c_56252, plain, (![B_3769, C_3770]: (v3_pre_topc('#skF_3'('#skF_5', B_3769, C_3770), '#skF_5') | ~r1_xboole_0(B_3769, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_3769)=C_3770 | ~m1_subset_1(C_3770, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3769, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_56248])).
% 21.15/11.44  tff(c_56309, plain, (![B_3780, C_3781]: (v3_pre_topc('#skF_3'('#skF_5', B_3780, C_3781), '#skF_5') | ~r1_xboole_0(B_3780, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3780)=C_3781 | ~m1_subset_1(C_3781, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3780, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_52499, c_35061, c_56252])).
% 21.15/11.44  tff(c_56343, plain, (![B_3782]: (v3_pre_topc('#skF_3'('#skF_5', B_3782, '#skF_7'), '#skF_5') | ~r1_xboole_0(B_3782, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3782)='#skF_7' | ~m1_subset_1(B_3782, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_56309])).
% 21.15/11.44  tff(c_56376, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_56343])).
% 21.15/11.44  tff(c_56392, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_52168, c_56376])).
% 21.15/11.44  tff(c_56393, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_7'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_35045, c_56392])).
% 21.15/11.44  tff(c_56394, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_56393])).
% 21.15/11.44  tff(c_56397, plain, (k4_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_56394])).
% 21.15/11.44  tff(c_56404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_56397])).
% 21.15/11.44  tff(c_56406, plain, (r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_56393])).
% 21.15/11.44  tff(c_52557, plain, (![A_3459, C_3460, B_3461]: (~v2_struct_0(A_3459) | ~r2_hidden(C_3460, k2_pre_topc(A_3459, B_3461)) | ~m1_subset_1(C_3460, u1_struct_0(A_3459)) | ~m1_subset_1(B_3461, k1_zfmisc_1(u1_struct_0(A_3459))) | ~l1_pre_topc(A_3459))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_52563, plain, (![C_3460]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3460, k1_xboole_0) | ~m1_subset_1(C_3460, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52168, c_52557])).
% 21.15/11.44  tff(c_52573, plain, (![C_3460]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3460, k1_xboole_0) | ~m1_subset_1(C_3460, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_35061, c_35061, c_52563])).
% 21.15/11.44  tff(c_52578, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_52573])).
% 21.15/11.44  tff(c_52226, plain, (![B_3435]: (k2_pre_topc('#skF_5', B_3435)=k2_struct_0('#skF_5') | ~v1_tops_1(B_3435, '#skF_5') | ~m1_subset_1(B_3435, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_52232, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_52226])).
% 21.15/11.44  tff(c_52246, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_52232])).
% 21.15/11.44  tff(c_52723, plain, (![C_3483, A_3484, B_3485]: (r2_hidden(C_3483, '#skF_4'(A_3484, B_3485, C_3483)) | r2_hidden(C_3483, k2_pre_topc(A_3484, B_3485)) | v2_struct_0(A_3484) | ~m1_subset_1(C_3483, u1_struct_0(A_3484)) | ~m1_subset_1(B_3485, k1_zfmisc_1(u1_struct_0(A_3484))) | ~l1_pre_topc(A_3484))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_52725, plain, (![C_3483, B_3485]: (r2_hidden(C_3483, '#skF_4'('#skF_5', B_3485, C_3483)) | r2_hidden(C_3483, k2_pre_topc('#skF_5', B_3485)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3483, u1_struct_0('#skF_5')) | ~m1_subset_1(B_3485, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_52723])).
% 21.15/11.44  tff(c_52733, plain, (![C_3483, B_3485]: (r2_hidden(C_3483, '#skF_4'('#skF_5', B_3485, C_3483)) | r2_hidden(C_3483, k2_pre_topc('#skF_5', B_3485)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3483, k2_struct_0('#skF_5')) | ~m1_subset_1(B_3485, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_52725])).
% 21.15/11.44  tff(c_52965, plain, (![C_3518, B_3519]: (r2_hidden(C_3518, '#skF_4'('#skF_5', B_3519, C_3518)) | r2_hidden(C_3518, k2_pre_topc('#skF_5', B_3519)) | ~m1_subset_1(C_3518, k2_struct_0('#skF_5')) | ~m1_subset_1(B_3519, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52578, c_52733])).
% 21.15/11.44  tff(c_52969, plain, (![C_3518]: (r2_hidden(C_3518, '#skF_4'('#skF_5', '#skF_6', C_3518)) | r2_hidden(C_3518, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_3518, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_35062, c_52965])).
% 21.15/11.44  tff(c_53000, plain, (![C_3523]: (r2_hidden(C_3523, '#skF_4'('#skF_5', '#skF_6', C_3523)) | r2_hidden(C_3523, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3523, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52246, c_52969])).
% 21.15/11.44  tff(c_53199, plain, (![C_3542, A_3543]: (r2_hidden(C_3542, A_3543) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_3542), k1_zfmisc_1(A_3543)) | r2_hidden(C_3542, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3542, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_53000, c_26])).
% 21.15/11.44  tff(c_53203, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_53199])).
% 21.15/11.44  tff(c_53210, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_52246, c_35061, c_53203])).
% 21.15/11.44  tff(c_53211, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52578, c_53210])).
% 21.15/11.44  tff(c_53387, plain, (![B_3568, D_3569, C_3570, A_3571]: (~r1_xboole_0(B_3568, D_3569) | ~r2_hidden(C_3570, D_3569) | ~v3_pre_topc(D_3569, A_3571) | ~m1_subset_1(D_3569, k1_zfmisc_1(u1_struct_0(A_3571))) | ~r2_hidden(C_3570, k2_pre_topc(A_3571, B_3568)) | ~m1_subset_1(C_3570, u1_struct_0(A_3571)) | ~m1_subset_1(B_3568, k1_zfmisc_1(u1_struct_0(A_3571))) | ~l1_pre_topc(A_3571))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_53469, plain, (![C_3575, A_3576]: (~r2_hidden(C_3575, '#skF_7') | ~v3_pre_topc('#skF_7', A_3576) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_3576))) | ~r2_hidden(C_3575, k2_pre_topc(A_3576, '#skF_6')) | ~m1_subset_1(C_3575, u1_struct_0(A_3576)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_3576))) | ~l1_pre_topc(A_3576))), inference(resolution, [status(thm)], [c_35050, c_53387])).
% 21.15/11.44  tff(c_53471, plain, (![C_3575]: (~r2_hidden(C_3575, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_3575, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_3575, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_53469])).
% 21.15/11.44  tff(c_53474, plain, (![C_3577]: (~r2_hidden(C_3577, '#skF_7') | ~r2_hidden(C_3577, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3577, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35062, c_35061, c_35061, c_52246, c_35068, c_35048, c_53471])).
% 21.15/11.44  tff(c_53483, plain, (![C_3578]: (~r2_hidden(C_3578, '#skF_7') | ~m1_subset_1(C_3578, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_53211, c_53474])).
% 21.15/11.44  tff(c_53494, plain, (![A_2199]: (~r2_hidden(A_2199, '#skF_7'))), inference(resolution, [status(thm)], [c_35373, c_53483])).
% 21.15/11.44  tff(c_54678, plain, (![A_3680, B_3681, C_3682, E_3683]: (r2_hidden('#skF_2'(A_3680, B_3681, C_3682), C_3682) | ~r1_xboole_0(B_3681, E_3683) | ~r2_hidden('#skF_2'(A_3680, B_3681, C_3682), E_3683) | ~v3_pre_topc(E_3683, A_3680) | ~m1_subset_1(E_3683, k1_zfmisc_1(u1_struct_0(A_3680))) | k2_pre_topc(A_3680, B_3681)=C_3682 | ~m1_subset_1(C_3682, k1_zfmisc_1(u1_struct_0(A_3680))) | ~m1_subset_1(B_3681, k1_zfmisc_1(u1_struct_0(A_3680))) | ~l1_pre_topc(A_3680))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_54724, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_34, c_54678])).
% 21.15/11.44  tff(c_56605, plain, (![A_3787, B_3788, C_3789]: (r2_hidden('#skF_2'(A_3787, B_3788, C_3789), C_3789) | ~r1_xboole_0(B_3788, u1_struct_0(A_3787)) | ~v3_pre_topc(u1_struct_0(A_3787), A_3787) | k2_pre_topc(A_3787, B_3788)=C_3789 | ~m1_subset_1(C_3789, k1_zfmisc_1(u1_struct_0(A_3787))) | ~m1_subset_1(B_3788, k1_zfmisc_1(u1_struct_0(A_3787))) | ~l1_pre_topc(A_3787))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_54724])).
% 21.15/11.44  tff(c_56609, plain, (![B_3788, C_3789]: (r2_hidden('#skF_2'('#skF_5', B_3788, C_3789), C_3789) | ~r1_xboole_0(B_3788, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_3788)=C_3789 | ~m1_subset_1(C_3789, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3788, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_35061, c_56605])).
% 21.15/11.44  tff(c_57079, plain, (![B_3808, C_3809]: (r2_hidden('#skF_2'('#skF_5', B_3808, C_3809), C_3809) | ~r1_xboole_0(B_3808, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3808)=C_3809 | ~m1_subset_1(C_3809, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3808, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35061, c_35061, c_52499, c_35061, c_56609])).
% 21.15/11.44  tff(c_57094, plain, (![B_3808]: (r2_hidden('#skF_2'('#skF_5', B_3808, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_3808, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3808)='#skF_7' | ~m1_subset_1(B_3808, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_57079])).
% 21.15/11.44  tff(c_57115, plain, (![B_3810]: (~r1_xboole_0(B_3810, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3810)='#skF_7' | ~m1_subset_1(B_3810, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_53494, c_57094])).
% 21.15/11.44  tff(c_57148, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_28, c_57115])).
% 21.15/11.44  tff(c_57165, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_52168, c_56406, c_57148])).
% 21.15/11.44  tff(c_57167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35045, c_57165])).
% 21.15/11.44  tff(c_57169, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_52573])).
% 21.15/11.44  tff(c_52567, plain, (![C_3460]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3460, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3460, u1_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_45878, c_52557])).
% 21.15/11.44  tff(c_52577, plain, (![C_3460]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3460, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3460, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_121, c_35061, c_35061, c_52567])).
% 21.15/11.44  tff(c_57207, plain, (![C_3460]: (~r2_hidden(C_3460, k2_struct_0('#skF_5')) | ~m1_subset_1(C_3460, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_57169, c_52577])).
% 21.15/11.44  tff(c_57259, plain, (![B_3835, C_3836]: (~m1_subset_1('#skF_2'('#skF_5', B_3835, C_3836), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_3835)=C_3836 | ~m1_subset_1(C_3836, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3835, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_57221, c_57207])).
% 21.15/11.44  tff(c_57268, plain, (![B_3837, C_3838]: (k2_pre_topc('#skF_5', B_3837)=C_3838 | ~m1_subset_1(C_3838, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_3837, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_57231, c_57259])).
% 21.15/11.44  tff(c_57283, plain, (![B_3839]: (k2_pre_topc('#skF_5', B_3839)='#skF_7' | ~m1_subset_1(B_3839, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_35068, c_57268])).
% 21.15/11.44  tff(c_57300, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_35062, c_57283])).
% 21.15/11.44  tff(c_57303, plain, (k2_struct_0('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_57300, c_52246])).
% 21.15/11.44  tff(c_57305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52224, c_57303])).
% 21.15/11.44  tff(c_57307, plain, (k2_struct_0('#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_52198])).
% 21.15/11.44  tff(c_57323, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_57307, c_35062])).
% 21.15/11.44  tff(c_35497, plain, (![B_2214]: (k2_pre_topc('#skF_5', B_2214)=k2_struct_0('#skF_5') | ~v1_tops_1(B_2214, '#skF_5') | ~m1_subset_1(B_2214, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_57456, plain, (![B_3845]: (k2_pre_topc('#skF_5', B_3845)='#skF_7' | ~v1_tops_1(B_3845, '#skF_5') | ~m1_subset_1(B_3845, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_57307, c_57307, c_35497])).
% 21.15/11.44  tff(c_57459, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_7' | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_57323, c_57456])).
% 21.15/11.44  tff(c_57470, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_57459])).
% 21.15/11.44  tff(c_57324, plain, (u1_struct_0('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_57307, c_35061])).
% 21.15/11.44  tff(c_70, plain, (![B_114, A_112]: (v4_pre_topc(B_114, A_112) | k2_pre_topc(A_112, B_114)!=B_114 | ~v2_pre_topc(A_112) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.15/11.44  tff(c_57354, plain, (![B_114]: (v4_pre_topc(B_114, '#skF_5') | k2_pre_topc('#skF_5', B_114)!=B_114 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_114, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57324, c_70])).
% 21.15/11.44  tff(c_58614, plain, (![B_3978]: (v4_pre_topc(B_3978, '#skF_5') | k2_pre_topc('#skF_5', B_3978)!=B_3978 | ~m1_subset_1(B_3978, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_100, c_57354])).
% 21.15/11.44  tff(c_58617, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_57323, c_58614])).
% 21.15/11.44  tff(c_58627, plain, (v4_pre_topc('#skF_6', '#skF_5') | '#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_57470, c_58617])).
% 21.15/11.44  tff(c_58628, plain, ('#skF_7'!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52170, c_58627])).
% 21.15/11.44  tff(c_58542, plain, (![A_3972, B_3973, C_3974]: (r2_hidden('#skF_2'(A_3972, B_3973, C_3974), u1_struct_0(A_3972)) | k2_pre_topc(A_3972, B_3973)=C_3974 | ~m1_subset_1(C_3974, k1_zfmisc_1(u1_struct_0(A_3972))) | ~m1_subset_1(B_3973, k1_zfmisc_1(u1_struct_0(A_3972))) | ~l1_pre_topc(A_3972))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_58550, plain, (![B_3973, C_3974]: (r2_hidden('#skF_2'('#skF_5', B_3973, C_3974), '#skF_7') | k2_pre_topc('#skF_5', B_3973)=C_3974 | ~m1_subset_1(C_3974, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3973, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57324, c_58542])).
% 21.15/11.44  tff(c_58703, plain, (![B_3987, C_3988]: (r2_hidden('#skF_2'('#skF_5', B_3987, C_3988), '#skF_7') | k2_pre_topc('#skF_5', B_3987)=C_3988 | ~m1_subset_1(C_3988, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3987, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_57324, c_57324, c_58550])).
% 21.15/11.44  tff(c_58713, plain, (![B_3987, C_3988]: (m1_subset_1('#skF_2'('#skF_5', B_3987, C_3988), '#skF_7') | k2_pre_topc('#skF_5', B_3987)=C_3988 | ~m1_subset_1(C_3988, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3987, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_58703, c_35375])).
% 21.15/11.44  tff(c_57631, plain, (![B_3861]: (v4_pre_topc(B_3861, '#skF_5') | k2_pre_topc('#skF_5', B_3861)!=B_3861 | ~m1_subset_1(B_3861, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_100, c_57354])).
% 21.15/11.44  tff(c_57634, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_57323, c_57631])).
% 21.15/11.44  tff(c_57644, plain, (v4_pre_topc('#skF_6', '#skF_5') | '#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_57470, c_57634])).
% 21.15/11.44  tff(c_57645, plain, ('#skF_7'!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52170, c_57644])).
% 21.15/11.44  tff(c_57513, plain, (![A_3849, C_3850, B_3851]: (~v2_struct_0(A_3849) | ~r2_hidden(C_3850, k2_pre_topc(A_3849, B_3851)) | ~m1_subset_1(C_3850, u1_struct_0(A_3849)) | ~m1_subset_1(B_3851, k1_zfmisc_1(u1_struct_0(A_3849))) | ~l1_pre_topc(A_3849))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_57517, plain, (![C_3850]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3850, k1_xboole_0) | ~m1_subset_1(C_3850, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52168, c_57513])).
% 21.15/11.44  tff(c_57523, plain, (![C_3850]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3850, k1_xboole_0) | ~m1_subset_1(C_3850, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_57324, c_57517])).
% 21.15/11.44  tff(c_57526, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_57523])).
% 21.15/11.44  tff(c_57958, plain, (![A_3902, B_3903, C_3904]: (m1_subset_1('#skF_4'(A_3902, B_3903, C_3904), k1_zfmisc_1(u1_struct_0(A_3902))) | r2_hidden(C_3904, k2_pre_topc(A_3902, B_3903)) | v2_struct_0(A_3902) | ~m1_subset_1(C_3904, u1_struct_0(A_3902)) | ~m1_subset_1(B_3903, k1_zfmisc_1(u1_struct_0(A_3902))) | ~l1_pre_topc(A_3902))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_57672, plain, (![C_3863, A_3864, B_3865]: (r2_hidden(C_3863, '#skF_4'(A_3864, B_3865, C_3863)) | r2_hidden(C_3863, k2_pre_topc(A_3864, B_3865)) | v2_struct_0(A_3864) | ~m1_subset_1(C_3863, u1_struct_0(A_3864)) | ~m1_subset_1(B_3865, k1_zfmisc_1(u1_struct_0(A_3864))) | ~l1_pre_topc(A_3864))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_57674, plain, (![C_3863, B_3865]: (r2_hidden(C_3863, '#skF_4'('#skF_5', B_3865, C_3863)) | r2_hidden(C_3863, k2_pre_topc('#skF_5', B_3865)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3863, u1_struct_0('#skF_5')) | ~m1_subset_1(B_3865, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57324, c_57672])).
% 21.15/11.44  tff(c_57682, plain, (![C_3863, B_3865]: (r2_hidden(C_3863, '#skF_4'('#skF_5', B_3865, C_3863)) | r2_hidden(C_3863, k2_pre_topc('#skF_5', B_3865)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3863, '#skF_7') | ~m1_subset_1(B_3865, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_57324, c_57674])).
% 21.15/11.44  tff(c_57730, plain, (![C_3872, B_3873]: (r2_hidden(C_3872, '#skF_4'('#skF_5', B_3873, C_3872)) | r2_hidden(C_3872, k2_pre_topc('#skF_5', B_3873)) | ~m1_subset_1(C_3872, '#skF_7') | ~m1_subset_1(B_3873, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_57526, c_57682])).
% 21.15/11.44  tff(c_57749, plain, (![C_3872]: (r2_hidden(C_3872, '#skF_4'('#skF_5', '#skF_6', C_3872)) | r2_hidden(C_3872, '#skF_7') | ~m1_subset_1(C_3872, '#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_57470, c_57730])).
% 21.15/11.44  tff(c_57801, plain, (![C_3879]: (r2_hidden(C_3879, '#skF_4'('#skF_5', '#skF_6', C_3879)) | r2_hidden(C_3879, '#skF_7') | ~m1_subset_1(C_3879, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_57323, c_57749])).
% 21.15/11.44  tff(c_57808, plain, (![C_3879, A_16]: (r2_hidden(C_3879, A_16) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_3879), k1_zfmisc_1(A_16)) | r2_hidden(C_3879, '#skF_7') | ~m1_subset_1(C_3879, '#skF_7'))), inference(resolution, [status(thm)], [c_57801, c_26])).
% 21.15/11.44  tff(c_57968, plain, (![C_3904]: (r2_hidden(C_3904, u1_struct_0('#skF_5')) | r2_hidden(C_3904, '#skF_7') | ~m1_subset_1(C_3904, '#skF_7') | r2_hidden(C_3904, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_3904, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_57958, c_57808])).
% 21.15/11.44  tff(c_58006, plain, (![C_3904]: (r2_hidden(C_3904, '#skF_7') | v2_struct_0('#skF_5') | ~m1_subset_1(C_3904, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_57323, c_57324, c_57324, c_57470, c_57324, c_57968])).
% 21.15/11.44  tff(c_58007, plain, (![C_3904]: (r2_hidden(C_3904, '#skF_7') | ~m1_subset_1(C_3904, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_57526, c_58006])).
% 21.15/11.44  tff(c_58369, plain, (![B_3948, D_3949, C_3950, A_3951]: (~r1_xboole_0(B_3948, D_3949) | ~r2_hidden(C_3950, D_3949) | ~v3_pre_topc(D_3949, A_3951) | ~m1_subset_1(D_3949, k1_zfmisc_1(u1_struct_0(A_3951))) | ~r2_hidden(C_3950, k2_pre_topc(A_3951, B_3948)) | ~m1_subset_1(C_3950, u1_struct_0(A_3951)) | ~m1_subset_1(B_3948, k1_zfmisc_1(u1_struct_0(A_3951))) | ~l1_pre_topc(A_3951))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.15/11.44  tff(c_58429, plain, (![C_3956, A_3957]: (~r2_hidden(C_3956, '#skF_7') | ~v3_pre_topc('#skF_7', A_3957) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_3957))) | ~r2_hidden(C_3956, k2_pre_topc(A_3957, '#skF_6')) | ~m1_subset_1(C_3956, u1_struct_0(A_3957)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_3957))) | ~l1_pre_topc(A_3957))), inference(resolution, [status(thm)], [c_35050, c_58369])).
% 21.15/11.44  tff(c_58431, plain, (![C_3956]: (~r2_hidden(C_3956, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | ~r2_hidden(C_3956, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_3956, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57324, c_58429])).
% 21.15/11.44  tff(c_58434, plain, (![C_3958]: (~r2_hidden(C_3958, '#skF_7') | ~m1_subset_1(C_3958, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_57323, c_57324, c_57324, c_57470, c_121, c_35048, c_58431])).
% 21.15/11.44  tff(c_58448, plain, (![C_3904]: (~m1_subset_1(C_3904, '#skF_7'))), inference(resolution, [status(thm)], [c_58007, c_58434])).
% 21.15/11.44  tff(c_57577, plain, (![A_3856, B_3857, C_3858]: (r2_hidden('#skF_2'(A_3856, B_3857, C_3858), u1_struct_0(A_3856)) | k2_pre_topc(A_3856, B_3857)=C_3858 | ~m1_subset_1(C_3858, k1_zfmisc_1(u1_struct_0(A_3856))) | ~m1_subset_1(B_3857, k1_zfmisc_1(u1_struct_0(A_3856))) | ~l1_pre_topc(A_3856))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.15/11.44  tff(c_57585, plain, (![B_3857, C_3858]: (r2_hidden('#skF_2'('#skF_5', B_3857, C_3858), '#skF_7') | k2_pre_topc('#skF_5', B_3857)=C_3858 | ~m1_subset_1(C_3858, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_3857, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57324, c_57577])).
% 21.15/11.44  tff(c_57722, plain, (![B_3870, C_3871]: (r2_hidden('#skF_2'('#skF_5', B_3870, C_3871), '#skF_7') | k2_pre_topc('#skF_5', B_3870)=C_3871 | ~m1_subset_1(C_3871, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3870, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_57324, c_57324, c_57585])).
% 21.15/11.44  tff(c_57728, plain, (![B_3870, C_3871]: (m1_subset_1('#skF_2'('#skF_5', B_3870, C_3871), '#skF_7') | k2_pre_topc('#skF_5', B_3870)=C_3871 | ~m1_subset_1(C_3871, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3870, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_57722, c_35375])).
% 21.15/11.44  tff(c_58459, plain, (![B_3961, C_3962]: (k2_pre_topc('#skF_5', B_3961)=C_3962 | ~m1_subset_1(C_3962, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3961, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_58448, c_57728])).
% 21.15/11.44  tff(c_58471, plain, (![B_3963]: (k2_pre_topc('#skF_5', B_3963)='#skF_6' | ~m1_subset_1(B_3963, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_57323, c_58459])).
% 21.15/11.44  tff(c_58483, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_57323, c_58471])).
% 21.15/11.44  tff(c_58499, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58483, c_57470])).
% 21.15/11.44  tff(c_58501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57645, c_58499])).
% 21.15/11.44  tff(c_58503, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_57523])).
% 21.15/11.44  tff(c_57519, plain, (![C_3850]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3850, '#skF_7') | ~m1_subset_1(C_3850, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_51989, c_57513])).
% 21.15/11.44  tff(c_57525, plain, (![C_3850]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_3850, '#skF_7') | ~m1_subset_1(C_3850, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_121, c_57324, c_57324, c_57519])).
% 21.15/11.44  tff(c_58523, plain, (![C_3850]: (~r2_hidden(C_3850, '#skF_7') | ~m1_subset_1(C_3850, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58503, c_57525])).
% 21.15/11.44  tff(c_58729, plain, (![B_3994, C_3995]: (~m1_subset_1('#skF_2'('#skF_5', B_3994, C_3995), '#skF_7') | k2_pre_topc('#skF_5', B_3994)=C_3995 | ~m1_subset_1(C_3995, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3994, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_58703, c_58523])).
% 21.15/11.44  tff(c_58734, plain, (![B_3996, C_3997]: (k2_pre_topc('#skF_5', B_3996)=C_3997 | ~m1_subset_1(C_3997, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_3996, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_58713, c_58729])).
% 21.15/11.44  tff(c_58746, plain, (![B_3998]: (k2_pre_topc('#skF_5', B_3998)='#skF_6' | ~m1_subset_1(B_3998, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_57323, c_58734])).
% 21.15/11.44  tff(c_58758, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_57323, c_58746])).
% 21.15/11.44  tff(c_58761, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58758, c_57470])).
% 21.15/11.44  tff(c_58763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58628, c_58761])).
% 21.15/11.44  tff(c_58764, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_45937])).
% 21.15/11.44  tff(c_58810, plain, (![B_4002]: (k2_pre_topc('#skF_5', B_4002)=k2_struct_0('#skF_5') | ~v1_tops_1(B_4002, '#skF_5') | ~m1_subset_1(B_4002, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35487])).
% 21.15/11.44  tff(c_58816, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_35062, c_58810])).
% 21.15/11.44  tff(c_58829, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_35046, c_58764, c_58816])).
% 21.15/11.44  tff(c_35289, plain, (k4_xboole_0(k2_struct_0('#skF_5'), '#skF_7')=k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_35068, c_35276])).
% 21.15/11.44  tff(c_35106, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | k4_xboole_0(A_8, B_9)!=A_8)), inference(resolution, [status(thm)], [c_16, c_35096])).
% 21.15/11.44  tff(c_35443, plain, (k3_xboole_0(k2_struct_0('#skF_5'), '#skF_7')=k1_xboole_0 | k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')!=k2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35289, c_35106])).
% 21.15/11.44  tff(c_35480, plain, (k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')!=k2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_35443])).
% 21.15/11.44  tff(c_35069, plain, (![A_2170, B_2171]: (k4_xboole_0(A_2170, B_2171)=A_2170 | ~r1_xboole_0(A_2170, B_2171))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.15/11.44  tff(c_35076, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_35069])).
% 21.15/11.44  tff(c_35440, plain, (k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')=k2_struct_0('#skF_5') | k3_xboole_0(k2_struct_0('#skF_5'), '#skF_7')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35289, c_35076])).
% 21.15/11.44  tff(c_35483, plain, (k3_xboole_0(k2_struct_0('#skF_5'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_35480, c_35440])).
% 21.15/11.44  tff(c_58840, plain, (k3_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58829, c_35483])).
% 21.15/11.44  tff(c_58857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35108, c_58840])).
% 21.15/11.44  tff(c_58859, plain, (k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_35443])).
% 21.15/11.44  tff(c_35228, plain, (![A_2190, B_2191]: (k3_subset_1(A_2190, k3_subset_1(A_2190, B_2191))=B_2191 | ~m1_subset_1(B_2191, k1_zfmisc_1(A_2190)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.15/11.44  tff(c_35237, plain, (k3_subset_1(k2_struct_0('#skF_5'), k3_subset_1(k2_struct_0('#skF_5'), '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_35068, c_35228])).
% 21.15/11.44  tff(c_58869, plain, (k3_subset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58859, c_35237])).
% 21.15/11.44  tff(c_35240, plain, (![A_20]: (k3_subset_1(A_20, k3_subset_1(A_20, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_35228])).
% 21.15/11.44  tff(c_35294, plain, (![A_20]: (k3_subset_1(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35293, c_35240])).
% 21.15/11.44  tff(c_58897, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_58869, c_35294])).
% 21.15/11.44  tff(c_58903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35045, c_58897])).
% 21.15/11.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.15/11.44  
% 21.15/11.44  Inference rules
% 21.15/11.44  ----------------------
% 21.15/11.44  #Ref     : 0
% 21.15/11.44  #Sup     : 12542
% 21.15/11.44  #Fact    : 20
% 21.15/11.44  #Define  : 0
% 21.15/11.44  #Split   : 236
% 21.15/11.44  #Chain   : 0
% 21.15/11.44  #Close   : 0
% 21.15/11.44  
% 21.15/11.44  Ordering : KBO
% 21.15/11.44  
% 21.15/11.44  Simplification rules
% 21.15/11.44  ----------------------
% 21.15/11.44  #Subsume      : 2294
% 21.15/11.44  #Demod        : 12722
% 21.15/11.44  #Tautology    : 3215
% 21.15/11.44  #SimpNegUnit  : 1176
% 21.15/11.44  #BackRed      : 759
% 21.15/11.44  
% 21.15/11.44  #Partial instantiations: 0
% 21.15/11.44  #Strategies tried      : 1
% 21.15/11.45  
% 21.15/11.45  Timing (in seconds)
% 21.15/11.45  ----------------------
% 21.15/11.45  Preprocessing        : 0.48
% 21.15/11.45  Parsing              : 0.24
% 21.15/11.45  CNF conversion       : 0.05
% 21.15/11.45  Main loop            : 9.97
% 21.15/11.45  Inferencing          : 2.69
% 21.15/11.45  Reduction            : 3.39
% 21.15/11.45  Demodulation         : 2.35
% 21.15/11.45  BG Simplification    : 0.24
% 21.15/11.45  Subsumption          : 2.97
% 21.15/11.45  Abstraction          : 0.35
% 21.15/11.45  MUC search           : 0.00
% 21.15/11.45  Cooper               : 0.00
% 21.15/11.45  Total                : 10.64
% 21.15/11.45  Index Insertion      : 0.00
% 21.15/11.45  Index Deletion       : 0.00
% 21.15/11.45  Index Matching       : 0.00
% 21.15/11.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
