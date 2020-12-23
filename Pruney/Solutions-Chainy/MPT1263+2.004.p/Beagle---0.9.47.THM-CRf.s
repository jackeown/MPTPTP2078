%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 15.52s
% Output     : CNFRefutation 16.08s
% Verified   : 
% Statistics : Number of formulae       :  421 (8599 expanded)
%              Number of leaves         :   54 (3012 expanded)
%              Depth                    :   29
%              Number of atoms          : 1126 (24346 expanded)
%              Number of equality atoms :  239 (5420 expanded)
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

tff(f_184,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_116,axiom,(
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

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_93,axiom,(
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

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_58,axiom,(
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

tff(f_139,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(c_96,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_104,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_165,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_66,plain,(
    ! [A_111] :
      ( l1_struct_0(A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_166,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = k2_struct_0(A_159)
      | ~ l1_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_172,plain,(
    ! [A_162] :
      ( u1_struct_0(A_162) = k2_struct_0(A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_66,c_166])).

tff(c_176,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_172])).

tff(c_94,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_177,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_94])).

tff(c_533,plain,(
    ! [B_201,A_202] :
      ( v1_tops_1(B_201,A_202)
      | k2_pre_topc(A_202,B_201) != k2_struct_0(A_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_536,plain,(
    ! [B_201] :
      ( v1_tops_1(B_201,'#skF_5')
      | k2_pre_topc('#skF_5',B_201) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_533])).

tff(c_786,plain,(
    ! [B_220] :
      ( v1_tops_1(B_220,'#skF_5')
      | k2_pre_topc('#skF_5',B_220) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_536])).

tff(c_789,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_786])).

tff(c_800,plain,(
    k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_789])).

tff(c_16,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_496,plain,(
    ! [A_197,B_198] :
      ( k2_pre_topc(A_197,B_198) = B_198
      | ~ v4_pre_topc(B_198,A_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_526,plain,(
    ! [A_200] :
      ( k2_pre_topc(A_200,u1_struct_0(A_200)) = u1_struct_0(A_200)
      | ~ v4_pre_topc(u1_struct_0(A_200),A_200)
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_119,c_496])).

tff(c_529,plain,
    ( k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) = u1_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_526])).

tff(c_531,plain,
    ( k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_176,c_176,c_529])).

tff(c_532,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [A_171,B_172] : k4_xboole_0(A_171,k4_xboole_0(A_171,B_172)) = k3_xboole_0(A_171,B_172) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_250,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_246])).

tff(c_363,plain,(
    ! [A_179,B_180] :
      ( k4_xboole_0(A_179,B_180) = k3_subset_1(A_179,B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_369,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_subset_1(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_119,c_363])).

tff(c_375,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_369])).

tff(c_751,plain,(
    ! [B_216,A_217] :
      ( v4_pre_topc(B_216,A_217)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_217),B_216),A_217)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_759,plain,(
    ! [A_217] :
      ( v4_pre_topc(u1_struct_0(A_217),A_217)
      | ~ v3_pre_topc(k1_xboole_0,A_217)
      | ~ m1_subset_1(u1_struct_0(A_217),k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_751])).

tff(c_775,plain,(
    ! [A_219] :
      ( v4_pre_topc(u1_struct_0(A_219),A_219)
      | ~ v3_pre_topc(k1_xboole_0,A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_759])).

tff(c_781,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_775])).

tff(c_784,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_781])).

tff(c_785,plain,(
    ~ v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_784])).

tff(c_1165,plain,(
    ! [A_245,B_246,C_247] :
      ( r2_hidden('#skF_2'(A_245,B_246,C_247),u1_struct_0(A_245))
      | k2_pre_topc(A_245,B_246) = C_247
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1176,plain,(
    ! [B_246,C_247] :
      ( r2_hidden('#skF_2'('#skF_5',B_246,C_247),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_246) = C_247
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_1165])).

tff(c_1181,plain,(
    ! [B_246,C_247] :
      ( r2_hidden('#skF_2'('#skF_5',B_246,C_247),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_246) = C_247
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_176,c_176,c_1176])).

tff(c_1807,plain,(
    ! [B_307,A_308,C_309] :
      ( r1_xboole_0(B_307,'#skF_3'(A_308,B_307,C_309))
      | ~ r2_hidden('#skF_2'(A_308,B_307,C_309),C_309)
      | k2_pre_topc(A_308,B_307) = C_309
      | ~ m1_subset_1(C_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1822,plain,(
    ! [B_246] :
      ( r1_xboole_0(B_246,'#skF_3'('#skF_5',B_246,k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_246) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1181,c_1807])).

tff(c_1830,plain,(
    ! [B_246] :
      ( r1_xboole_0(B_246,'#skF_3'('#skF_5',B_246,k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_246) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_1822])).

tff(c_1911,plain,(
    ! [A_321,B_322,C_323] :
      ( v3_pre_topc('#skF_3'(A_321,B_322,C_323),A_321)
      | ~ r2_hidden('#skF_2'(A_321,B_322,C_323),C_323)
      | k2_pre_topc(A_321,B_322) = C_323
      | ~ m1_subset_1(C_323,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1932,plain,(
    ! [B_246] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_246,k2_struct_0('#skF_5')),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_246) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1181,c_1911])).

tff(c_1942,plain,(
    ! [B_246] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_246,k2_struct_0('#skF_5')),'#skF_5')
      | k2_pre_topc('#skF_5',B_246) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_1932])).

tff(c_2230,plain,(
    ! [A_341,B_342,C_343] :
      ( m1_subset_1('#skF_3'(A_341,B_342,C_343),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ r2_hidden('#skF_2'(A_341,B_342,C_343),C_343)
      | k2_pre_topc(A_341,B_342) = C_343
      | ~ m1_subset_1(C_343,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2251,plain,(
    ! [B_246] :
      ( m1_subset_1('#skF_3'('#skF_5',B_246,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_246) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1181,c_2230])).

tff(c_2265,plain,(
    ! [B_344] :
      ( m1_subset_1('#skF_3'('#skF_5',B_344,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_344) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_176,c_2251])).

tff(c_118,plain,(
    ! [C_151] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_405,plain,(
    ! [C_151] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_118])).

tff(c_406,plain,(
    ! [C_151] :
      ( ~ r1_xboole_0('#skF_6',C_151)
      | ~ v3_pre_topc(C_151,'#skF_5')
      | k1_xboole_0 = C_151
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_405])).

tff(c_2472,plain,(
    ! [B_362] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_362,k2_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_362,k2_struct_0('#skF_5')),'#skF_5')
      | '#skF_3'('#skF_5',B_362,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_362) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_362,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_2265,c_406])).

tff(c_10417,plain,(
    ! [B_710] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_710,k2_struct_0('#skF_5')))
      | '#skF_3'('#skF_5',B_710,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_710) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_710,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1942,c_2472])).

tff(c_10421,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1830,c_10417])).

tff(c_10427,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_10421])).

tff(c_10428,plain,(
    '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_800,c_10427])).

tff(c_10460,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10428,c_1942])).

tff(c_10491,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_10460])).

tff(c_10493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_800,c_785,c_10491])).

tff(c_10495,plain,(
    v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_10880,plain,(
    ! [A_738,B_739] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_738),B_739),A_738)
      | ~ v4_pre_topc(B_739,A_738)
      | ~ m1_subset_1(B_739,k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ l1_pre_topc(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10891,plain,(
    ! [A_738] :
      ( v3_pre_topc(k1_xboole_0,A_738)
      | ~ v4_pre_topc(u1_struct_0(A_738),A_738)
      | ~ m1_subset_1(u1_struct_0(A_738),k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ l1_pre_topc(A_738) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_10880])).

tff(c_10912,plain,(
    ! [A_741] :
      ( v3_pre_topc(k1_xboole_0,A_741)
      | ~ v4_pre_topc(u1_struct_0(A_741),A_741)
      | ~ l1_pre_topc(A_741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_10891])).

tff(c_10918,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_10912])).

tff(c_10921,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10495,c_10918])).

tff(c_26,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_372,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k3_subset_1(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_363])).

tff(c_377,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_372])).

tff(c_10496,plain,(
    ! [B_711,A_712] :
      ( v1_tops_1(B_711,A_712)
      | k2_pre_topc(A_712,B_711) != k2_struct_0(A_712)
      | ~ m1_subset_1(B_711,k1_zfmisc_1(u1_struct_0(A_712)))
      | ~ l1_pre_topc(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10499,plain,(
    ! [B_711] :
      ( v1_tops_1(B_711,'#skF_5')
      | k2_pre_topc('#skF_5',B_711) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_711,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_10496])).

tff(c_10781,plain,(
    ! [B_733] :
      ( v1_tops_1(B_733,'#skF_5')
      | k2_pre_topc('#skF_5',B_733) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_733,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_10499])).

tff(c_10784,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_10781])).

tff(c_10795,plain,(
    k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_10784])).

tff(c_11140,plain,(
    ! [A_756,B_757,C_758] :
      ( r2_hidden('#skF_2'(A_756,B_757,C_758),u1_struct_0(A_756))
      | k2_pre_topc(A_756,B_757) = C_758
      | ~ m1_subset_1(C_758,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ l1_pre_topc(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11151,plain,(
    ! [B_757,C_758] :
      ( r2_hidden('#skF_2'('#skF_5',B_757,C_758),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_757) = C_758
      | ~ m1_subset_1(C_758,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_11140])).

tff(c_11156,plain,(
    ! [B_757,C_758] :
      ( r2_hidden('#skF_2'('#skF_5',B_757,C_758),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_757) = C_758
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_176,c_176,c_11151])).

tff(c_11766,plain,(
    ! [B_819,A_820,C_821] :
      ( r1_xboole_0(B_819,'#skF_3'(A_820,B_819,C_821))
      | ~ r2_hidden('#skF_2'(A_820,B_819,C_821),C_821)
      | k2_pre_topc(A_820,B_819) = C_821
      | ~ m1_subset_1(C_821,k1_zfmisc_1(u1_struct_0(A_820)))
      | ~ m1_subset_1(B_819,k1_zfmisc_1(u1_struct_0(A_820)))
      | ~ l1_pre_topc(A_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11779,plain,(
    ! [B_757] :
      ( r1_xboole_0(B_757,'#skF_3'('#skF_5',B_757,k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_757) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_11156,c_11766])).

tff(c_11787,plain,(
    ! [B_757] :
      ( r1_xboole_0(B_757,'#skF_3'('#skF_5',B_757,k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_757) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_11779])).

tff(c_11932,plain,(
    ! [A_830,B_831,C_832] :
      ( v3_pre_topc('#skF_3'(A_830,B_831,C_832),A_830)
      | ~ r2_hidden('#skF_2'(A_830,B_831,C_832),C_832)
      | k2_pre_topc(A_830,B_831) = C_832
      | ~ m1_subset_1(C_832,k1_zfmisc_1(u1_struct_0(A_830)))
      | ~ m1_subset_1(B_831,k1_zfmisc_1(u1_struct_0(A_830)))
      | ~ l1_pre_topc(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11951,plain,(
    ! [B_757] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_757,k2_struct_0('#skF_5')),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_757) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_11156,c_11932])).

tff(c_11961,plain,(
    ! [B_757] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_757,k2_struct_0('#skF_5')),'#skF_5')
      | k2_pre_topc('#skF_5',B_757) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_11951])).

tff(c_12200,plain,(
    ! [A_860,B_861,C_862] :
      ( m1_subset_1('#skF_3'(A_860,B_861,C_862),k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ r2_hidden('#skF_2'(A_860,B_861,C_862),C_862)
      | k2_pre_topc(A_860,B_861) = C_862
      | ~ m1_subset_1(C_862,k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ m1_subset_1(B_861,k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ l1_pre_topc(A_860) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12216,plain,(
    ! [B_757] :
      ( m1_subset_1('#skF_3'('#skF_5',B_757,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_757) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_11156,c_12200])).

tff(c_12229,plain,(
    ! [B_863] :
      ( m1_subset_1('#skF_3'('#skF_5',B_863,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_863) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_863,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_96,c_176,c_119,c_176,c_176,c_12216])).

tff(c_12284,plain,(
    ! [B_868] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_868,k2_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_868,k2_struct_0('#skF_5')),'#skF_5')
      | '#skF_3'('#skF_5',B_868,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_868) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_868,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_12229,c_406])).

tff(c_15632,plain,(
    ! [B_1063] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_1063,k2_struct_0('#skF_5')))
      | '#skF_3'('#skF_5',B_1063,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_1063) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1063,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_11961,c_12284])).

tff(c_15636,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_11787,c_15632])).

tff(c_15642,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_15636])).

tff(c_15643,plain,(
    '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10795,c_15642])).

tff(c_36,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),'#skF_3'(A_26,B_70,C_92))
      | ~ r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15658,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15643,c_36])).

tff(c_15677,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_177,c_176,c_119,c_176,c_15658])).

tff(c_15678,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_10795,c_15677])).

tff(c_15704,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15678])).

tff(c_15713,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_11156,c_15704])).

tff(c_15718,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_119,c_15713])).

tff(c_15720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10795,c_15718])).

tff(c_15721,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_15678])).

tff(c_437,plain,(
    ! [A_187,C_188,B_189] :
      ( m1_subset_1(A_187,C_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(C_188))
      | ~ r2_hidden(A_187,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_446,plain,(
    ! [A_187,A_20] :
      ( m1_subset_1(A_187,A_20)
      | ~ r2_hidden(A_187,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_437])).

tff(c_15776,plain,(
    ! [A_1067] : m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_1067) ),
    inference(resolution,[status(thm)],[c_15721,c_446])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16146,plain,(
    ! [A_1075] : k4_xboole_0(A_1075,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) = k3_subset_1(A_1075,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_15776,c_18])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16181,plain,(
    k3_subset_1(k1_xboole_0,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16146,c_14])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k3_subset_1(A_14,k3_subset_1(A_14,B_15)) = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15888,plain,(
    ! [A_14] : k3_subset_1(A_14,k3_subset_1(A_14,'#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')))) = '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_15776,c_22])).

tff(c_16215,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16181,c_15888])).

tff(c_16223,plain,(
    '#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_16215])).

tff(c_15771,plain,(
    ! [A_20] : m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_20) ),
    inference(resolution,[status(thm)],[c_15721,c_446])).

tff(c_16232,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16223,c_15771])).

tff(c_24,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_15749,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_16)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_15721,c_24])).

tff(c_15775,plain,(
    ! [A_16] : r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_15749])).

tff(c_16231,plain,(
    ! [A_16] : r2_hidden(k1_xboole_0,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16223,c_15775])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12029,plain,(
    ! [B_843,D_844,C_845,A_846] :
      ( ~ r1_xboole_0(B_843,D_844)
      | ~ r2_hidden(C_845,D_844)
      | ~ v3_pre_topc(D_844,A_846)
      | ~ m1_subset_1(D_844,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ r2_hidden(C_845,k2_pre_topc(A_846,B_843))
      | ~ m1_subset_1(C_845,u1_struct_0(A_846))
      | ~ m1_subset_1(B_843,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ l1_pre_topc(A_846) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16538,plain,(
    ! [C_1081,B_1082,A_1083,A_1084] :
      ( ~ r2_hidden(C_1081,B_1082)
      | ~ v3_pre_topc(B_1082,A_1083)
      | ~ m1_subset_1(B_1082,k1_zfmisc_1(u1_struct_0(A_1083)))
      | ~ r2_hidden(C_1081,k2_pre_topc(A_1083,A_1084))
      | ~ m1_subset_1(C_1081,u1_struct_0(A_1083))
      | ~ m1_subset_1(A_1084,k1_zfmisc_1(u1_struct_0(A_1083)))
      | ~ l1_pre_topc(A_1083)
      | k3_xboole_0(A_1084,B_1082) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_12029])).

tff(c_16540,plain,(
    ! [A_16,A_1083,A_1084] :
      ( ~ v3_pre_topc(A_16,A_1083)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(u1_struct_0(A_1083)))
      | ~ r2_hidden(k1_xboole_0,k2_pre_topc(A_1083,A_1084))
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_1083))
      | ~ m1_subset_1(A_1084,k1_zfmisc_1(u1_struct_0(A_1083)))
      | ~ l1_pre_topc(A_1083)
      | k3_xboole_0(A_1084,A_16) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16231,c_16538])).

tff(c_16634,plain,(
    ! [A_1088,A_1089,A_1090] :
      ( ~ v3_pre_topc(A_1088,A_1089)
      | ~ m1_subset_1(A_1088,k1_zfmisc_1(u1_struct_0(A_1089)))
      | ~ m1_subset_1(A_1090,k1_zfmisc_1(u1_struct_0(A_1089)))
      | ~ l1_pre_topc(A_1089)
      | k3_xboole_0(A_1090,A_1088) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16232,c_16231,c_16540])).

tff(c_16637,plain,(
    ! [A_1089,A_1090] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1089)
      | ~ m1_subset_1(A_1090,k1_zfmisc_1(u1_struct_0(A_1089)))
      | ~ l1_pre_topc(A_1089)
      | k3_xboole_0(A_1090,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16232,c_16634])).

tff(c_16666,plain,(
    ! [A_1091,A_1092] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1091)
      | ~ m1_subset_1(A_1092,k1_zfmisc_1(u1_struct_0(A_1091)))
      | ~ l1_pre_topc(A_1091) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16637])).

tff(c_16700,plain,(
    ! [A_1093] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1093)
      | ~ l1_pre_topc(A_1093) ) ),
    inference(resolution,[status(thm)],[c_16232,c_16666])).

tff(c_16703,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10921,c_16700])).

tff(c_16707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16703])).

tff(c_16708,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_16791,plain,(
    ! [A_1106,B_1107] : k4_xboole_0(A_1106,k4_xboole_0(A_1106,B_1107)) = k3_xboole_0(A_1106,B_1107) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16820,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_16791])).

tff(c_16825,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16820])).

tff(c_16943,plain,(
    ! [A_1119,B_1120] :
      ( k4_xboole_0(A_1119,B_1120) = k3_subset_1(A_1119,B_1120)
      | ~ m1_subset_1(B_1120,k1_zfmisc_1(A_1119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16952,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_subset_1(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_119,c_16943])).

tff(c_16959,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16825,c_16952])).

tff(c_16759,plain,(
    ! [A_1102,B_1103] : k5_xboole_0(A_1102,k3_xboole_0(A_1102,B_1103)) = k4_xboole_0(A_1102,B_1103) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16771,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16759])).

tff(c_16774,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16771])).

tff(c_16709,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_100,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_16710,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_16712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_16710])).

tff(c_16713,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_16737,plain,(
    ! [A_1098,B_1099] :
      ( k3_xboole_0(A_1098,B_1099) = k1_xboole_0
      | ~ r1_xboole_0(A_1098,B_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16745,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16713,c_16737])).

tff(c_16768,plain,(
    k5_xboole_0('#skF_6',k1_xboole_0) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16745,c_16759])).

tff(c_16785,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16774,c_16768])).

tff(c_16718,plain,(
    ! [A_1094] :
      ( u1_struct_0(A_1094) = k2_struct_0(A_1094)
      | ~ l1_struct_0(A_1094) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16725,plain,(
    ! [A_1095] :
      ( u1_struct_0(A_1095) = k2_struct_0(A_1095)
      | ~ l1_pre_topc(A_1095) ) ),
    inference(resolution,[status(thm)],[c_66,c_16718])).

tff(c_16729,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_16725])).

tff(c_16731,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16729,c_94])).

tff(c_17176,plain,(
    ! [A_1137,B_1138] :
      ( k2_pre_topc(A_1137,B_1138) = k2_struct_0(A_1137)
      | ~ v1_tops_1(B_1138,A_1137)
      | ~ m1_subset_1(B_1138,k1_zfmisc_1(u1_struct_0(A_1137)))
      | ~ l1_pre_topc(A_1137) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_17179,plain,(
    ! [B_1138] :
      ( k2_pre_topc('#skF_5',B_1138) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1138,'#skF_5')
      | ~ m1_subset_1(B_1138,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17176])).

tff(c_24720,plain,(
    ! [B_1625] :
      ( k2_pre_topc('#skF_5',B_1625) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1625,'#skF_5')
      | ~ m1_subset_1(B_1625,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17179])).

tff(c_24723,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_24720])).

tff(c_24737,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_24723])).

tff(c_17159,plain,(
    ! [A_1134,B_1135] :
      ( k2_pre_topc(A_1134,B_1135) = B_1135
      | ~ v4_pre_topc(B_1135,A_1134)
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(u1_struct_0(A_1134)))
      | ~ l1_pre_topc(A_1134) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_17162,plain,(
    ! [B_1135] :
      ( k2_pre_topc('#skF_5',B_1135) = B_1135
      | ~ v4_pre_topc(B_1135,'#skF_5')
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17159])).

tff(c_24405,plain,(
    ! [B_1600] :
      ( k2_pre_topc('#skF_5',B_1600) = B_1600
      | ~ v4_pre_topc(B_1600,'#skF_5')
      | ~ m1_subset_1(B_1600,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17162])).

tff(c_24420,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_24405])).

tff(c_24426,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24420])).

tff(c_98,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_24672,plain,(
    ! [B_1621,A_1622] :
      ( v4_pre_topc(B_1621,A_1622)
      | k2_pre_topc(A_1622,B_1621) != B_1621
      | ~ v2_pre_topc(A_1622)
      | ~ m1_subset_1(B_1621,k1_zfmisc_1(u1_struct_0(A_1622)))
      | ~ l1_pre_topc(A_1622) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24675,plain,(
    ! [B_1621] :
      ( v4_pre_topc(B_1621,'#skF_5')
      | k2_pre_topc('#skF_5',B_1621) != B_1621
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_1621,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_24672])).

tff(c_24693,plain,(
    ! [B_1624] :
      ( v4_pre_topc(B_1624,'#skF_5')
      | k2_pre_topc('#skF_5',B_1624) != B_1624
      | ~ m1_subset_1(B_1624,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_98,c_24675])).

tff(c_24696,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_16731,c_24693])).

tff(c_24710,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24426,c_24696])).

tff(c_24744,plain,(
    k2_struct_0('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24737,c_24710])).

tff(c_29610,plain,(
    ! [A_1947,B_1948,C_1949] :
      ( r2_hidden('#skF_2'(A_1947,B_1948,C_1949),u1_struct_0(A_1947))
      | k2_pre_topc(A_1947,B_1948) = C_1949
      | ~ m1_subset_1(C_1949,k1_zfmisc_1(u1_struct_0(A_1947)))
      | ~ m1_subset_1(B_1948,k1_zfmisc_1(u1_struct_0(A_1947)))
      | ~ l1_pre_topc(A_1947) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_29618,plain,(
    ! [B_1948,C_1949] :
      ( r2_hidden('#skF_2'('#skF_5',B_1948,C_1949),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1948) = C_1949
      | ~ m1_subset_1(C_1949,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1948,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_29610])).

tff(c_29976,plain,(
    ! [B_1968,C_1969] :
      ( r2_hidden('#skF_2'('#skF_5',B_1968,C_1969),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1968) = C_1969
      | ~ m1_subset_1(C_1969,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1968,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_29618])).

tff(c_16845,plain,(
    ! [A_1109,C_1110,B_1111] :
      ( m1_subset_1(A_1109,C_1110)
      | ~ m1_subset_1(B_1111,k1_zfmisc_1(C_1110))
      | ~ r2_hidden(A_1109,B_1111) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16856,plain,(
    ! [A_1109,A_13] :
      ( m1_subset_1(A_1109,A_13)
      | ~ r2_hidden(A_1109,A_13) ) ),
    inference(resolution,[status(thm)],[c_119,c_16845])).

tff(c_29987,plain,(
    ! [B_1968,C_1969] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1968,C_1969),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1968) = C_1969
      | ~ m1_subset_1(C_1969,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1968,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_29976,c_16856])).

tff(c_16801,plain,(
    ! [B_1107] : k3_xboole_0(k1_xboole_0,B_1107) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16791,c_14])).

tff(c_88,plain,(
    ! [A_140] :
      ( v3_pre_topc(k2_struct_0(A_140),A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_24425,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_24405])).

tff(c_24443,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24425])).

tff(c_16955,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = k3_subset_1(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_16943])).

tff(c_16961,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16955])).

tff(c_24542,plain,(
    ! [B_1611,A_1612] :
      ( v4_pre_topc(B_1611,A_1612)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1612),B_1611),A_1612)
      | ~ m1_subset_1(B_1611,k1_zfmisc_1(u1_struct_0(A_1612)))
      | ~ l1_pre_topc(A_1612) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_24549,plain,(
    ! [A_1612] :
      ( v4_pre_topc(k1_xboole_0,A_1612)
      | ~ v3_pre_topc(u1_struct_0(A_1612),A_1612)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1612)))
      | ~ l1_pre_topc(A_1612) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16961,c_24542])).

tff(c_24594,plain,(
    ! [A_1614] :
      ( v4_pre_topc(k1_xboole_0,A_1614)
      | ~ v3_pre_topc(u1_struct_0(A_1614),A_1614)
      | ~ l1_pre_topc(A_1614) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24549])).

tff(c_24600,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_24594])).

tff(c_24603,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_24600])).

tff(c_24604,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24443,c_24603])).

tff(c_24607,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_24604])).

tff(c_24611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_24607])).

tff(c_24612,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24425])).

tff(c_106,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_16724,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_106])).

tff(c_16730,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16729,c_16724])).

tff(c_16855,plain,(
    ! [A_1109] :
      ( m1_subset_1(A_1109,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_1109,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16730,c_16845])).

tff(c_24843,plain,(
    ! [A_1632,C_1633,B_1634] :
      ( ~ v2_struct_0(A_1632)
      | ~ r2_hidden(C_1633,k2_pre_topc(A_1632,B_1634))
      | ~ m1_subset_1(C_1633,u1_struct_0(A_1632))
      | ~ m1_subset_1(B_1634,k1_zfmisc_1(u1_struct_0(A_1632)))
      | ~ l1_pre_topc(A_1632) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24849,plain,(
    ! [C_1633] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1633,k1_xboole_0)
      | ~ m1_subset_1(C_1633,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24612,c_24843])).

tff(c_24857,plain,(
    ! [C_1633] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1633,k1_xboole_0)
      | ~ m1_subset_1(C_1633,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_26,c_16729,c_16729,c_24849])).

tff(c_24860,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24857])).

tff(c_78,plain,(
    ! [A_115,B_127,C_133] :
      ( m1_subset_1('#skF_4'(A_115,B_127,C_133),k1_zfmisc_1(u1_struct_0(A_115)))
      | r2_hidden(C_133,k2_pre_topc(A_115,B_127))
      | v2_struct_0(A_115)
      | ~ m1_subset_1(C_133,u1_struct_0(A_115))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25285,plain,(
    ! [C_1653,A_1654,B_1655] :
      ( r2_hidden(C_1653,'#skF_4'(A_1654,B_1655,C_1653))
      | r2_hidden(C_1653,k2_pre_topc(A_1654,B_1655))
      | v2_struct_0(A_1654)
      | ~ m1_subset_1(C_1653,u1_struct_0(A_1654))
      | ~ m1_subset_1(B_1655,k1_zfmisc_1(u1_struct_0(A_1654)))
      | ~ l1_pre_topc(A_1654) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25287,plain,(
    ! [C_1653,B_1655] :
      ( r2_hidden(C_1653,'#skF_4'('#skF_5',B_1655,C_1653))
      | r2_hidden(C_1653,k2_pre_topc('#skF_5',B_1655))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1653,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1655,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_25285])).

tff(c_25295,plain,(
    ! [C_1653,B_1655] :
      ( r2_hidden(C_1653,'#skF_4'('#skF_5',B_1655,C_1653))
      | r2_hidden(C_1653,k2_pre_topc('#skF_5',B_1655))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1653,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1655,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_25287])).

tff(c_25590,plain,(
    ! [C_1703,B_1704] :
      ( r2_hidden(C_1703,'#skF_4'('#skF_5',B_1704,C_1703))
      | r2_hidden(C_1703,k2_pre_topc('#skF_5',B_1704))
      | ~ m1_subset_1(C_1703,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1704,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24860,c_25295])).

tff(c_25592,plain,(
    ! [C_1703] :
      ( r2_hidden(C_1703,'#skF_4'('#skF_5','#skF_6',C_1703))
      | r2_hidden(C_1703,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1703,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16731,c_25590])).

tff(c_25608,plain,(
    ! [C_1705] :
      ( r2_hidden(C_1705,'#skF_4'('#skF_5','#skF_6',C_1705))
      | r2_hidden(C_1705,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1705,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24737,c_25592])).

tff(c_25810,plain,(
    ! [C_1723,A_1724] :
      ( r2_hidden(C_1723,A_1724)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1723),k1_zfmisc_1(A_1724))
      | r2_hidden(C_1723,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1723,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25608,c_24])).

tff(c_25814,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_25810])).

tff(c_25821,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16731,c_16729,c_16729,c_24737,c_16729,c_25814])).

tff(c_25822,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24860,c_25821])).

tff(c_102,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_16717,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_102])).

tff(c_25873,plain,(
    ! [B_1732,D_1733,C_1734,A_1735] :
      ( ~ r1_xboole_0(B_1732,D_1733)
      | ~ r2_hidden(C_1734,D_1733)
      | ~ v3_pre_topc(D_1733,A_1735)
      | ~ m1_subset_1(D_1733,k1_zfmisc_1(u1_struct_0(A_1735)))
      | ~ r2_hidden(C_1734,k2_pre_topc(A_1735,B_1732))
      | ~ m1_subset_1(C_1734,u1_struct_0(A_1735))
      | ~ m1_subset_1(B_1732,k1_zfmisc_1(u1_struct_0(A_1735)))
      | ~ l1_pre_topc(A_1735) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25937,plain,(
    ! [C_1739,A_1740] :
      ( ~ r2_hidden(C_1739,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_1740)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_1740)))
      | ~ r2_hidden(C_1739,k2_pre_topc(A_1740,'#skF_6'))
      | ~ m1_subset_1(C_1739,u1_struct_0(A_1740))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1740)))
      | ~ l1_pre_topc(A_1740) ) ),
    inference(resolution,[status(thm)],[c_16713,c_25873])).

tff(c_25939,plain,(
    ! [C_1739] :
      ( ~ r2_hidden(C_1739,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_1739,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1739,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_25937])).

tff(c_25942,plain,(
    ! [C_1741] :
      ( ~ r2_hidden(C_1741,'#skF_7')
      | ~ r2_hidden(C_1741,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1741,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16731,c_16729,c_16729,c_24737,c_16730,c_16717,c_25939])).

tff(c_25951,plain,(
    ! [C_1742] :
      ( ~ r2_hidden(C_1742,'#skF_7')
      | ~ m1_subset_1(C_1742,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25822,c_25942])).

tff(c_25959,plain,(
    ! [A_1109] : ~ r2_hidden(A_1109,'#skF_7') ),
    inference(resolution,[status(thm)],[c_16855,c_25951])).

tff(c_24613,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_24425])).

tff(c_24625,plain,(
    ! [A_1615,B_1616] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_1615),B_1616),A_1615)
      | ~ v4_pre_topc(B_1616,A_1615)
      | ~ m1_subset_1(B_1616,k1_zfmisc_1(u1_struct_0(A_1615)))
      | ~ l1_pre_topc(A_1615) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_24629,plain,(
    ! [A_1615] :
      ( v3_pre_topc(u1_struct_0(A_1615),A_1615)
      | ~ v4_pre_topc(k1_xboole_0,A_1615)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1615)))
      | ~ l1_pre_topc(A_1615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16961,c_24625])).

tff(c_24644,plain,(
    ! [A_1617] :
      ( v3_pre_topc(u1_struct_0(A_1617),A_1617)
      | ~ v4_pre_topc(k1_xboole_0,A_1617)
      | ~ l1_pre_topc(A_1617) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24629])).

tff(c_24647,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_24644])).

tff(c_24649,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_24613,c_24647])).

tff(c_32,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),u1_struct_0(A_26))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28008,plain,(
    ! [A_1870,B_1871,C_1872,E_1873] :
      ( r2_hidden('#skF_2'(A_1870,B_1871,C_1872),C_1872)
      | ~ r1_xboole_0(B_1871,E_1873)
      | ~ r2_hidden('#skF_2'(A_1870,B_1871,C_1872),E_1873)
      | ~ v3_pre_topc(E_1873,A_1870)
      | ~ m1_subset_1(E_1873,k1_zfmisc_1(u1_struct_0(A_1870)))
      | k2_pre_topc(A_1870,B_1871) = C_1872
      | ~ m1_subset_1(C_1872,k1_zfmisc_1(u1_struct_0(A_1870)))
      | ~ m1_subset_1(B_1871,k1_zfmisc_1(u1_struct_0(A_1870)))
      | ~ l1_pre_topc(A_1870) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28062,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_28008])).

tff(c_29473,plain,(
    ! [A_1936,B_1937,C_1938] :
      ( r2_hidden('#skF_2'(A_1936,B_1937,C_1938),C_1938)
      | ~ r1_xboole_0(B_1937,u1_struct_0(A_1936))
      | ~ v3_pre_topc(u1_struct_0(A_1936),A_1936)
      | k2_pre_topc(A_1936,B_1937) = C_1938
      | ~ m1_subset_1(C_1938,k1_zfmisc_1(u1_struct_0(A_1936)))
      | ~ m1_subset_1(B_1937,k1_zfmisc_1(u1_struct_0(A_1936)))
      | ~ l1_pre_topc(A_1936) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_28062])).

tff(c_29477,plain,(
    ! [B_1937,C_1938] :
      ( r2_hidden('#skF_2'('#skF_5',B_1937,C_1938),C_1938)
      | ~ r1_xboole_0(B_1937,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_1937) = C_1938
      | ~ m1_subset_1(C_1938,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1937,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_29473])).

tff(c_29512,plain,(
    ! [B_1942,C_1943] :
      ( r2_hidden('#skF_2'('#skF_5',B_1942,C_1943),C_1943)
      | ~ r1_xboole_0(B_1942,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1942) = C_1943
      | ~ m1_subset_1(C_1943,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1942,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_24649,c_16729,c_29477])).

tff(c_29527,plain,(
    ! [B_1942] :
      ( r2_hidden('#skF_2'('#skF_5',B_1942,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_1942,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1942) = '#skF_7'
      | ~ m1_subset_1(B_1942,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_16730,c_29512])).

tff(c_29545,plain,(
    ! [B_1944] :
      ( ~ r1_xboole_0(B_1944,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1944) = '#skF_7'
      | ~ m1_subset_1(B_1944,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25959,c_29527])).

tff(c_29575,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_26,c_29545])).

tff(c_29589,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24612,c_29575])).

tff(c_29590,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_16708,c_29589])).

tff(c_29593,plain,(
    k3_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_29590])).

tff(c_29597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16801,c_29593])).

tff(c_29599,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_24857])).

tff(c_17193,plain,(
    ! [A_1140] :
      ( k2_pre_topc(A_1140,u1_struct_0(A_1140)) = u1_struct_0(A_1140)
      | ~ v4_pre_topc(u1_struct_0(A_1140),A_1140)
      | ~ l1_pre_topc(A_1140) ) ),
    inference(resolution,[status(thm)],[c_119,c_17159])).

tff(c_17196,plain,
    ( k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) = u1_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17193])).

tff(c_17198,plain,
    ( k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_17196])).

tff(c_17199,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17198])).

tff(c_17570,plain,(
    ! [B_1170] :
      ( k2_pre_topc('#skF_5',B_1170) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1170,'#skF_5')
      | ~ m1_subset_1(B_1170,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17179])).

tff(c_17573,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_17570])).

tff(c_17587,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_17573])).

tff(c_17208,plain,(
    ! [B_1142] :
      ( k2_pre_topc('#skF_5',B_1142) = B_1142
      | ~ v4_pre_topc(B_1142,'#skF_5')
      | ~ m1_subset_1(B_1142,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17162])).

tff(c_17223,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_17208])).

tff(c_17243,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17223])).

tff(c_17475,plain,(
    ! [B_1162,A_1163] :
      ( v4_pre_topc(B_1162,A_1163)
      | k2_pre_topc(A_1163,B_1162) != B_1162
      | ~ v2_pre_topc(A_1163)
      | ~ m1_subset_1(B_1162,k1_zfmisc_1(u1_struct_0(A_1163)))
      | ~ l1_pre_topc(A_1163) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_17478,plain,(
    ! [B_1162] :
      ( v4_pre_topc(B_1162,'#skF_5')
      | k2_pre_topc('#skF_5',B_1162) != B_1162
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_1162,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17475])).

tff(c_17496,plain,(
    ! [B_1165] :
      ( v4_pre_topc(B_1165,'#skF_5')
      | k2_pre_topc('#skF_5',B_1165) != B_1165
      | ~ m1_subset_1(B_1165,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_98,c_17478])).

tff(c_17499,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_16731,c_17496])).

tff(c_17513,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_17243,c_17499])).

tff(c_17602,plain,(
    k2_struct_0('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17587,c_17513])).

tff(c_23221,plain,(
    ! [A_1518,B_1519,C_1520] :
      ( r2_hidden('#skF_2'(A_1518,B_1519,C_1520),u1_struct_0(A_1518))
      | k2_pre_topc(A_1518,B_1519) = C_1520
      | ~ m1_subset_1(C_1520,k1_zfmisc_1(u1_struct_0(A_1518)))
      | ~ m1_subset_1(B_1519,k1_zfmisc_1(u1_struct_0(A_1518)))
      | ~ l1_pre_topc(A_1518) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_23229,plain,(
    ! [B_1519,C_1520] :
      ( r2_hidden('#skF_2'('#skF_5',B_1519,C_1520),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1519) = C_1520
      | ~ m1_subset_1(C_1520,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1519,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_23221])).

tff(c_23538,plain,(
    ! [B_1536,C_1537] :
      ( r2_hidden('#skF_2'('#skF_5',B_1536,C_1537),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1536) = C_1537
      | ~ m1_subset_1(C_1537,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1536,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_23229])).

tff(c_23549,plain,(
    ! [B_1536,C_1537] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1536,C_1537),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1536) = C_1537
      | ~ m1_subset_1(C_1537,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1536,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_23538,c_16856])).

tff(c_17226,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_17208])).

tff(c_17244,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17226])).

tff(c_17405,plain,(
    ! [B_1157,A_1158] :
      ( v4_pre_topc(B_1157,A_1158)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1158),B_1157),A_1158)
      | ~ m1_subset_1(B_1157,k1_zfmisc_1(u1_struct_0(A_1158)))
      | ~ l1_pre_topc(A_1158) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_17412,plain,(
    ! [A_1158] :
      ( v4_pre_topc(k1_xboole_0,A_1158)
      | ~ v3_pre_topc(u1_struct_0(A_1158),A_1158)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1158)))
      | ~ l1_pre_topc(A_1158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16961,c_17405])).

tff(c_17427,plain,(
    ! [A_1159] :
      ( v4_pre_topc(k1_xboole_0,A_1159)
      | ~ v3_pre_topc(u1_struct_0(A_1159),A_1159)
      | ~ l1_pre_topc(A_1159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_17412])).

tff(c_17433,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17427])).

tff(c_17436,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17433])).

tff(c_17437,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_17244,c_17436])).

tff(c_17440,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_17437])).

tff(c_17444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_17440])).

tff(c_17445,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_17226])).

tff(c_17446,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_17226])).

tff(c_17546,plain,(
    ! [A_1167,B_1168] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_1167),B_1168),A_1167)
      | ~ v4_pre_topc(B_1168,A_1167)
      | ~ m1_subset_1(B_1168,k1_zfmisc_1(u1_struct_0(A_1167)))
      | ~ l1_pre_topc(A_1167) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_17550,plain,(
    ! [A_1167] :
      ( v3_pre_topc(u1_struct_0(A_1167),A_1167)
      | ~ v4_pre_topc(k1_xboole_0,A_1167)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1167)))
      | ~ l1_pre_topc(A_1167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16961,c_17546])).

tff(c_17564,plain,(
    ! [A_1169] :
      ( v3_pre_topc(u1_struct_0(A_1169),A_1169)
      | ~ v4_pre_topc(k1_xboole_0,A_1169)
      | ~ l1_pre_topc(A_1169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_17550])).

tff(c_17567,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17564])).

tff(c_17569,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17446,c_17567])).

tff(c_20214,plain,(
    ! [A_1380,B_1381,C_1382,E_1383] :
      ( v3_pre_topc('#skF_3'(A_1380,B_1381,C_1382),A_1380)
      | ~ r1_xboole_0(B_1381,E_1383)
      | ~ r2_hidden('#skF_2'(A_1380,B_1381,C_1382),E_1383)
      | ~ v3_pre_topc(E_1383,A_1380)
      | ~ m1_subset_1(E_1383,k1_zfmisc_1(u1_struct_0(A_1380)))
      | k2_pre_topc(A_1380,B_1381) = C_1382
      | ~ m1_subset_1(C_1382,k1_zfmisc_1(u1_struct_0(A_1380)))
      | ~ m1_subset_1(B_1381,k1_zfmisc_1(u1_struct_0(A_1380)))
      | ~ l1_pre_topc(A_1380) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20267,plain,(
    ! [A_26,B_70,C_92] :
      ( v3_pre_topc('#skF_3'(A_26,B_70,C_92),A_26)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_20214])).

tff(c_22620,plain,(
    ! [A_1490,B_1491,C_1492] :
      ( v3_pre_topc('#skF_3'(A_1490,B_1491,C_1492),A_1490)
      | ~ r1_xboole_0(B_1491,u1_struct_0(A_1490))
      | ~ v3_pre_topc(u1_struct_0(A_1490),A_1490)
      | k2_pre_topc(A_1490,B_1491) = C_1492
      | ~ m1_subset_1(C_1492,k1_zfmisc_1(u1_struct_0(A_1490)))
      | ~ m1_subset_1(B_1491,k1_zfmisc_1(u1_struct_0(A_1490)))
      | ~ l1_pre_topc(A_1490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_20267])).

tff(c_22624,plain,(
    ! [B_1491,C_1492] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1491,C_1492),'#skF_5')
      | ~ r1_xboole_0(B_1491,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_1491) = C_1492
      | ~ m1_subset_1(C_1492,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1491,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_22620])).

tff(c_22631,plain,(
    ! [B_1493,C_1494] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1493,C_1494),'#skF_5')
      | ~ r1_xboole_0(B_1493,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1493) = C_1494
      | ~ m1_subset_1(C_1494,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1493,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_17569,c_16729,c_22624])).

tff(c_22662,plain,(
    ! [B_1495] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1495,'#skF_6'),'#skF_5')
      | ~ r1_xboole_0(B_1495,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1495) = '#skF_6'
      | ~ m1_subset_1(B_1495,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_16731,c_22631])).

tff(c_22692,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_6'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_22662])).

tff(c_22704,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_6'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17445,c_22692])).

tff(c_22710,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_22704])).

tff(c_22721,plain,(
    k3_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_22710])).

tff(c_22725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16801,c_22721])).

tff(c_22727,plain,(
    r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_22704])).

tff(c_17803,plain,(
    ! [A_1183,C_1184,B_1185] :
      ( ~ v2_struct_0(A_1183)
      | ~ r2_hidden(C_1184,k2_pre_topc(A_1183,B_1185))
      | ~ m1_subset_1(C_1184,u1_struct_0(A_1183))
      | ~ m1_subset_1(B_1185,k1_zfmisc_1(u1_struct_0(A_1183)))
      | ~ l1_pre_topc(A_1183) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_17809,plain,(
    ! [C_1184] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1184,k1_xboole_0)
      | ~ m1_subset_1(C_1184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17445,c_17803])).

tff(c_17815,plain,(
    ! [C_1184] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1184,k1_xboole_0)
      | ~ m1_subset_1(C_1184,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_26,c_16729,c_16729,c_17809])).

tff(c_17816,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17815])).

tff(c_18174,plain,(
    ! [C_1207,A_1208,B_1209] :
      ( r2_hidden(C_1207,'#skF_4'(A_1208,B_1209,C_1207))
      | r2_hidden(C_1207,k2_pre_topc(A_1208,B_1209))
      | v2_struct_0(A_1208)
      | ~ m1_subset_1(C_1207,u1_struct_0(A_1208))
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(u1_struct_0(A_1208)))
      | ~ l1_pre_topc(A_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_18176,plain,(
    ! [C_1207,B_1209] :
      ( r2_hidden(C_1207,'#skF_4'('#skF_5',B_1209,C_1207))
      | r2_hidden(C_1207,k2_pre_topc('#skF_5',B_1209))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1207,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_18174])).

tff(c_18184,plain,(
    ! [C_1207,B_1209] :
      ( r2_hidden(C_1207,'#skF_4'('#skF_5',B_1209,C_1207))
      | r2_hidden(C_1207,k2_pre_topc('#skF_5',B_1209))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1207,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1209,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_18176])).

tff(c_18454,plain,(
    ! [C_1248,B_1249] :
      ( r2_hidden(C_1248,'#skF_4'('#skF_5',B_1249,C_1248))
      | r2_hidden(C_1248,k2_pre_topc('#skF_5',B_1249))
      | ~ m1_subset_1(C_1248,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1249,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17816,c_18184])).

tff(c_18456,plain,(
    ! [C_1248] :
      ( r2_hidden(C_1248,'#skF_4'('#skF_5','#skF_6',C_1248))
      | r2_hidden(C_1248,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1248,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16731,c_18454])).

tff(c_18471,plain,(
    ! [C_1250] :
      ( r2_hidden(C_1250,'#skF_4'('#skF_5','#skF_6',C_1250))
      | r2_hidden(C_1250,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1250,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17587,c_18456])).

tff(c_18658,plain,(
    ! [C_1268,A_1269] :
      ( r2_hidden(C_1268,A_1269)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1268),k1_zfmisc_1(A_1269))
      | r2_hidden(C_1268,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1268,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18471,c_24])).

tff(c_18662,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,u1_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5'))
      | r2_hidden(C_133,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_18658])).

tff(c_18669,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16731,c_16729,c_16729,c_17587,c_16729,c_18662])).

tff(c_18670,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_133,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17816,c_18669])).

tff(c_18823,plain,(
    ! [B_1277,D_1278,C_1279,A_1280] :
      ( ~ r1_xboole_0(B_1277,D_1278)
      | ~ r2_hidden(C_1279,D_1278)
      | ~ v3_pre_topc(D_1278,A_1280)
      | ~ m1_subset_1(D_1278,k1_zfmisc_1(u1_struct_0(A_1280)))
      | ~ r2_hidden(C_1279,k2_pre_topc(A_1280,B_1277))
      | ~ m1_subset_1(C_1279,u1_struct_0(A_1280))
      | ~ m1_subset_1(B_1277,k1_zfmisc_1(u1_struct_0(A_1280)))
      | ~ l1_pre_topc(A_1280) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_18868,plain,(
    ! [C_1285,A_1286] :
      ( ~ r2_hidden(C_1285,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_1286)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_1286)))
      | ~ r2_hidden(C_1285,k2_pre_topc(A_1286,'#skF_6'))
      | ~ m1_subset_1(C_1285,u1_struct_0(A_1286))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1286)))
      | ~ l1_pre_topc(A_1286) ) ),
    inference(resolution,[status(thm)],[c_16713,c_18823])).

tff(c_18870,plain,(
    ! [C_1285] :
      ( ~ r2_hidden(C_1285,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_1285,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1285,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_18868])).

tff(c_18873,plain,(
    ! [C_1287] :
      ( ~ r2_hidden(C_1287,'#skF_7')
      | ~ r2_hidden(C_1287,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1287,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16731,c_16729,c_16729,c_17587,c_16730,c_16717,c_18870])).

tff(c_18882,plain,(
    ! [C_1288] :
      ( ~ r2_hidden(C_1288,'#skF_7')
      | ~ m1_subset_1(C_1288,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18670,c_18873])).

tff(c_18890,plain,(
    ! [A_1109] : ~ r2_hidden(A_1109,'#skF_7') ),
    inference(resolution,[status(thm)],[c_16855,c_18882])).

tff(c_20893,plain,(
    ! [A_1398,B_1399,C_1400,E_1401] :
      ( r2_hidden('#skF_2'(A_1398,B_1399,C_1400),C_1400)
      | ~ r1_xboole_0(B_1399,E_1401)
      | ~ r2_hidden('#skF_2'(A_1398,B_1399,C_1400),E_1401)
      | ~ v3_pre_topc(E_1401,A_1398)
      | ~ m1_subset_1(E_1401,k1_zfmisc_1(u1_struct_0(A_1398)))
      | k2_pre_topc(A_1398,B_1399) = C_1400
      | ~ m1_subset_1(C_1400,k1_zfmisc_1(u1_struct_0(A_1398)))
      | ~ m1_subset_1(B_1399,k1_zfmisc_1(u1_struct_0(A_1398)))
      | ~ l1_pre_topc(A_1398) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20949,plain,(
    ! [A_26,B_70,C_92] :
      ( r2_hidden('#skF_2'(A_26,B_70,C_92),C_92)
      | ~ r1_xboole_0(B_70,u1_struct_0(A_26))
      | ~ v3_pre_topc(u1_struct_0(A_26),A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | k2_pre_topc(A_26,B_70) = C_92
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_20893])).

tff(c_23035,plain,(
    ! [A_1507,B_1508,C_1509] :
      ( r2_hidden('#skF_2'(A_1507,B_1508,C_1509),C_1509)
      | ~ r1_xboole_0(B_1508,u1_struct_0(A_1507))
      | ~ v3_pre_topc(u1_struct_0(A_1507),A_1507)
      | k2_pre_topc(A_1507,B_1508) = C_1509
      | ~ m1_subset_1(C_1509,k1_zfmisc_1(u1_struct_0(A_1507)))
      | ~ m1_subset_1(B_1508,k1_zfmisc_1(u1_struct_0(A_1507)))
      | ~ l1_pre_topc(A_1507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_20949])).

tff(c_23039,plain,(
    ! [B_1508,C_1509] :
      ( r2_hidden('#skF_2'('#skF_5',B_1508,C_1509),C_1509)
      | ~ r1_xboole_0(B_1508,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | k2_pre_topc('#skF_5',B_1508) = C_1509
      | ~ m1_subset_1(C_1509,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1508,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_23035])).

tff(c_23129,plain,(
    ! [B_1512,C_1513] :
      ( r2_hidden('#skF_2'('#skF_5',B_1512,C_1513),C_1513)
      | ~ r1_xboole_0(B_1512,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1512) = C_1513
      | ~ m1_subset_1(C_1513,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1512,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_16729,c_17569,c_16729,c_23039])).

tff(c_23144,plain,(
    ! [B_1512] :
      ( r2_hidden('#skF_2'('#skF_5',B_1512,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_1512,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1512) = '#skF_7'
      | ~ m1_subset_1(B_1512,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_16730,c_23129])).

tff(c_23162,plain,(
    ! [B_1514] :
      ( ~ r1_xboole_0(B_1514,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1514) = '#skF_7'
      | ~ m1_subset_1(B_1514,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18890,c_23144])).

tff(c_23192,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_26,c_23162])).

tff(c_23205,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17445,c_22727,c_23192])).

tff(c_23207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16708,c_23205])).

tff(c_23209,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_17815])).

tff(c_17807,plain,(
    ! [C_1184] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1184,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1184,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17587,c_17803])).

tff(c_17813,plain,(
    ! [C_1184] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1184,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1184,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16731,c_16729,c_16729,c_17807])).

tff(c_23235,plain,(
    ! [C_1184] :
      ( ~ r2_hidden(C_1184,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1184,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23209,c_17813])).

tff(c_24086,plain,(
    ! [B_1578,C_1579] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_1578,C_1579),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1578) = C_1579
      | ~ m1_subset_1(C_1579,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1578,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_23538,c_23235])).

tff(c_24099,plain,(
    ! [B_1580,C_1581] :
      ( k2_pre_topc('#skF_5',B_1580) = C_1581
      | ~ m1_subset_1(C_1581,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1580,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_23549,c_24086])).

tff(c_24114,plain,(
    ! [B_1582] :
      ( k2_pre_topc('#skF_5',B_1582) = '#skF_6'
      | ~ m1_subset_1(B_1582,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_16731,c_24099])).

tff(c_24129,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_16731,c_24114])).

tff(c_24133,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24129,c_17587])).

tff(c_24135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17602,c_24133])).

tff(c_24136,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17223])).

tff(c_24219,plain,(
    ! [B_1589] :
      ( k2_pre_topc('#skF_5',B_1589) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1589,'#skF_5')
      | ~ m1_subset_1(B_1589,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17179])).

tff(c_24222,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_24219])).

tff(c_24236,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_24136,c_24222])).

tff(c_17201,plain,(
    ! [A_1141] :
      ( k2_pre_topc(A_1141,u1_struct_0(A_1141)) = k2_struct_0(A_1141)
      | ~ v1_tops_1(u1_struct_0(A_1141),A_1141)
      | ~ l1_pre_topc(A_1141) ) ),
    inference(resolution,[status(thm)],[c_119,c_17176])).

tff(c_17204,plain,
    ( k2_pre_topc('#skF_5',u1_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17201])).

tff(c_17206,plain,
    ( k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5')
    | ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16729,c_17204])).

tff(c_17207,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17206])).

tff(c_17227,plain,(
    ! [B_1143,A_1144] :
      ( v1_tops_1(B_1143,A_1144)
      | k2_pre_topc(A_1144,B_1143) != k2_struct_0(A_1144)
      | ~ m1_subset_1(B_1143,k1_zfmisc_1(u1_struct_0(A_1144)))
      | ~ l1_pre_topc(A_1144) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_17230,plain,(
    ! [B_1143] :
      ( v1_tops_1(B_1143,'#skF_5')
      | k2_pre_topc('#skF_5',B_1143) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1143,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_17227])).

tff(c_24162,plain,(
    ! [B_1585] :
      ( v1_tops_1(B_1585,'#skF_5')
      | k2_pre_topc('#skF_5',B_1585) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1585,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17230])).

tff(c_24172,plain,
    ( v1_tops_1(k2_struct_0('#skF_5'),'#skF_5')
    | k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_24162])).

tff(c_24182,plain,(
    k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_17207,c_24172])).

tff(c_24248,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24236,c_24236,c_24182])).

tff(c_24266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24136,c_24248])).

tff(c_24267,plain,(
    k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_17206])).

tff(c_24350,plain,(
    ! [B_1596,A_1597] :
      ( v4_pre_topc(B_1596,A_1597)
      | k2_pre_topc(A_1597,B_1596) != B_1596
      | ~ v2_pre_topc(A_1597)
      | ~ m1_subset_1(B_1596,k1_zfmisc_1(u1_struct_0(A_1597)))
      | ~ l1_pre_topc(A_1597) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24353,plain,(
    ! [B_1596] :
      ( v4_pre_topc(B_1596,'#skF_5')
      | k2_pre_topc('#skF_5',B_1596) != B_1596
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_1596,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16729,c_24350])).

tff(c_24367,plain,(
    ! [B_1598] :
      ( v4_pre_topc(B_1598,'#skF_5')
      | k2_pre_topc('#skF_5',B_1598) != B_1598
      | ~ m1_subset_1(B_1598,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_98,c_24353])).

tff(c_24377,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_24367])).

tff(c_24390,plain,(
    v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24267,c_24377])).

tff(c_24392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17199,c_24390])).

tff(c_24393,plain,(
    k2_pre_topc('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_17198])).

tff(c_24851,plain,(
    ! [C_1633] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1633,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1633,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24393,c_24843])).

tff(c_24859,plain,(
    ! [C_1633] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1633,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1633,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_119,c_16729,c_16729,c_24851])).

tff(c_29625,plain,(
    ! [C_1633] :
      ( ~ r2_hidden(C_1633,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1633,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29599,c_24859])).

tff(c_30623,plain,(
    ! [B_2011,C_2012] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_2011,C_2012),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_2011) = C_2012
      | ~ m1_subset_1(C_2012,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2011,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_29976,c_29625])).

tff(c_30636,plain,(
    ! [B_2013,C_2014] :
      ( k2_pre_topc('#skF_5',B_2013) = C_2014
      | ~ m1_subset_1(C_2014,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2013,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_29987,c_30623])).

tff(c_30651,plain,(
    ! [B_2015] :
      ( k2_pre_topc('#skF_5',B_2015) = '#skF_6'
      | ~ m1_subset_1(B_2015,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_16731,c_30636])).

tff(c_30666,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_16731,c_30651])).

tff(c_30670,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30666,c_24737])).

tff(c_30672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24744,c_30670])).

tff(c_30673,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_24420])).

tff(c_30713,plain,(
    ! [B_2020] :
      ( k2_pre_topc('#skF_5',B_2020) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_2020,'#skF_5')
      | ~ m1_subset_1(B_2020,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17179])).

tff(c_30716,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_16731,c_30713])).

tff(c_30730,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16709,c_30673,c_30716])).

tff(c_16957,plain,(
    k4_xboole_0(k2_struct_0('#skF_5'),'#skF_7') = k3_subset_1(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16730,c_16943])).

tff(c_30764,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30730,c_30730,c_16957])).

tff(c_30777,plain,(
    k3_subset_1('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16785,c_30764])).

tff(c_17005,plain,(
    ! [A_1125,B_1126] :
      ( k3_subset_1(A_1125,k3_subset_1(A_1125,B_1126)) = B_1126
      | ~ m1_subset_1(B_1126,k1_zfmisc_1(A_1125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17015,plain,(
    k3_subset_1(k2_struct_0('#skF_5'),k3_subset_1(k2_struct_0('#skF_5'),'#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_16730,c_17005])).

tff(c_30761,plain,(
    k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30730,c_30730,c_17015])).

tff(c_30845,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16959,c_30777,c_30761])).

tff(c_30846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16708,c_30845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.52/6.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/7.02  
% 15.57/7.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/7.02  %$ v4_pre_topc > v3_pre_topc > v1_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 15.57/7.02  
% 15.57/7.02  %Foreground sorts:
% 15.57/7.02  
% 15.57/7.02  
% 15.57/7.02  %Background operators:
% 15.57/7.02  
% 15.57/7.02  
% 15.57/7.02  %Foreground operators:
% 15.57/7.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.57/7.02  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 15.57/7.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.57/7.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.57/7.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.57/7.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.57/7.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.57/7.02  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.57/7.02  tff('#skF_7', type, '#skF_7': $i).
% 15.57/7.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.57/7.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.57/7.02  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.57/7.02  tff('#skF_5', type, '#skF_5': $i).
% 15.57/7.02  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 15.57/7.02  tff('#skF_6', type, '#skF_6': $i).
% 15.57/7.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.57/7.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.57/7.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.57/7.02  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.57/7.02  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.57/7.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.57/7.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.57/7.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.57/7.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.57/7.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.57/7.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.57/7.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.57/7.02  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 15.57/7.02  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.57/7.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.57/7.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.57/7.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.57/7.02  
% 16.08/7.07  tff(f_184, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(C = k1_xboole_0) & v3_pre_topc(C, A)) & r1_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tops_1)).
% 16.08/7.07  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 16.08/7.07  tff(f_97, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 16.08/7.07  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 16.08/7.07  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 16.08/7.07  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 16.08/7.07  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 16.08/7.07  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 16.08/7.07  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.08/7.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.08/7.07  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 16.08/7.07  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 16.08/7.07  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k2_pre_topc(A, B)) <=> (![D]: (r2_hidden(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(E, A) & r2_hidden(D, E)) & r1_xboole_0(B, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_pre_topc)).
% 16.08/7.07  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 16.08/7.07  tff(f_68, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 16.08/7.07  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 16.08/7.07  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.08/7.07  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 16.08/7.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.08/7.07  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_pre_topc)).
% 16.08/7.07  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 16.08/7.07  tff(f_154, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 16.08/7.07  tff(c_96, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_104, plain, (k1_xboole_0!='#skF_7' | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_165, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_104])).
% 16.08/7.07  tff(c_66, plain, (![A_111]: (l1_struct_0(A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.08/7.07  tff(c_166, plain, (![A_159]: (u1_struct_0(A_159)=k2_struct_0(A_159) | ~l1_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.08/7.07  tff(c_172, plain, (![A_162]: (u1_struct_0(A_162)=k2_struct_0(A_162) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_66, c_166])).
% 16.08/7.07  tff(c_176, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_96, c_172])).
% 16.08/7.07  tff(c_94, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_177, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_94])).
% 16.08/7.07  tff(c_533, plain, (![B_201, A_202]: (v1_tops_1(B_201, A_202) | k2_pre_topc(A_202, B_201)!=k2_struct_0(A_202) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.08/7.07  tff(c_536, plain, (![B_201]: (v1_tops_1(B_201, '#skF_5') | k2_pre_topc('#skF_5', B_201)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_201, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_533])).
% 16.08/7.07  tff(c_786, plain, (![B_220]: (v1_tops_1(B_220, '#skF_5') | k2_pre_topc('#skF_5', B_220)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_536])).
% 16.08/7.07  tff(c_789, plain, (v1_tops_1('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_177, c_786])).
% 16.08/7.07  tff(c_800, plain, (k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_165, c_789])).
% 16.08/7.07  tff(c_16, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.08/7.07  tff(c_20, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.08/7.07  tff(c_119, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 16.08/7.07  tff(c_496, plain, (![A_197, B_198]: (k2_pre_topc(A_197, B_198)=B_198 | ~v4_pre_topc(B_198, A_197) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.08/7.07  tff(c_526, plain, (![A_200]: (k2_pre_topc(A_200, u1_struct_0(A_200))=u1_struct_0(A_200) | ~v4_pre_topc(u1_struct_0(A_200), A_200) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_119, c_496])).
% 16.08/7.07  tff(c_529, plain, (k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))=u1_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_176, c_526])).
% 16.08/7.07  tff(c_531, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_176, c_176, c_529])).
% 16.08/7.07  tff(c_532, plain, (~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_531])).
% 16.08/7.07  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.08/7.07  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.08/7.07  tff(c_220, plain, (![A_171, B_172]: (k4_xboole_0(A_171, k4_xboole_0(A_171, B_172))=k3_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.08/7.07  tff(c_246, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_220])).
% 16.08/7.07  tff(c_250, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_246])).
% 16.08/7.07  tff(c_363, plain, (![A_179, B_180]: (k4_xboole_0(A_179, B_180)=k3_subset_1(A_179, B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.08/7.07  tff(c_369, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_subset_1(A_13, A_13))), inference(resolution, [status(thm)], [c_119, c_363])).
% 16.08/7.07  tff(c_375, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_369])).
% 16.08/7.07  tff(c_751, plain, (![B_216, A_217]: (v4_pre_topc(B_216, A_217) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_217), B_216), A_217) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_759, plain, (![A_217]: (v4_pre_topc(u1_struct_0(A_217), A_217) | ~v3_pre_topc(k1_xboole_0, A_217) | ~m1_subset_1(u1_struct_0(A_217), k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(superposition, [status(thm), theory('equality')], [c_375, c_751])).
% 16.08/7.07  tff(c_775, plain, (![A_219]: (v4_pre_topc(u1_struct_0(A_219), A_219) | ~v3_pre_topc(k1_xboole_0, A_219) | ~l1_pre_topc(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_759])).
% 16.08/7.07  tff(c_781, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_176, c_775])).
% 16.08/7.07  tff(c_784, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_781])).
% 16.08/7.07  tff(c_785, plain, (~v3_pre_topc(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_532, c_784])).
% 16.08/7.07  tff(c_1165, plain, (![A_245, B_246, C_247]: (r2_hidden('#skF_2'(A_245, B_246, C_247), u1_struct_0(A_245)) | k2_pre_topc(A_245, B_246)=C_247 | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_1176, plain, (![B_246, C_247]: (r2_hidden('#skF_2'('#skF_5', B_246, C_247), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_246)=C_247 | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_1165])).
% 16.08/7.07  tff(c_1181, plain, (![B_246, C_247]: (r2_hidden('#skF_2'('#skF_5', B_246, C_247), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_246)=C_247 | ~m1_subset_1(C_247, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_176, c_176, c_1176])).
% 16.08/7.07  tff(c_1807, plain, (![B_307, A_308, C_309]: (r1_xboole_0(B_307, '#skF_3'(A_308, B_307, C_309)) | ~r2_hidden('#skF_2'(A_308, B_307, C_309), C_309) | k2_pre_topc(A_308, B_307)=C_309 | ~m1_subset_1(C_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_1822, plain, (![B_246]: (r1_xboole_0(B_246, '#skF_3'('#skF_5', B_246, k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_246)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1181, c_1807])).
% 16.08/7.07  tff(c_1830, plain, (![B_246]: (r1_xboole_0(B_246, '#skF_3'('#skF_5', B_246, k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_246)=k2_struct_0('#skF_5') | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_1822])).
% 16.08/7.07  tff(c_1911, plain, (![A_321, B_322, C_323]: (v3_pre_topc('#skF_3'(A_321, B_322, C_323), A_321) | ~r2_hidden('#skF_2'(A_321, B_322, C_323), C_323) | k2_pre_topc(A_321, B_322)=C_323 | ~m1_subset_1(C_323, k1_zfmisc_1(u1_struct_0(A_321))) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_321))) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_1932, plain, (![B_246]: (v3_pre_topc('#skF_3'('#skF_5', B_246, k2_struct_0('#skF_5')), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_246)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1181, c_1911])).
% 16.08/7.07  tff(c_1942, plain, (![B_246]: (v3_pre_topc('#skF_3'('#skF_5', B_246, k2_struct_0('#skF_5')), '#skF_5') | k2_pre_topc('#skF_5', B_246)=k2_struct_0('#skF_5') | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_1932])).
% 16.08/7.07  tff(c_2230, plain, (![A_341, B_342, C_343]: (m1_subset_1('#skF_3'(A_341, B_342, C_343), k1_zfmisc_1(u1_struct_0(A_341))) | ~r2_hidden('#skF_2'(A_341, B_342, C_343), C_343) | k2_pre_topc(A_341, B_342)=C_343 | ~m1_subset_1(C_343, k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_2251, plain, (![B_246]: (m1_subset_1('#skF_3'('#skF_5', B_246, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_246)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1181, c_2230])).
% 16.08/7.07  tff(c_2265, plain, (![B_344]: (m1_subset_1('#skF_3'('#skF_5', B_344, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_344)=k2_struct_0('#skF_5') | ~m1_subset_1(B_344, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_176, c_2251])).
% 16.08/7.07  tff(c_118, plain, (![C_151]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_405, plain, (![C_151]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_118])).
% 16.08/7.07  tff(c_406, plain, (![C_151]: (~r1_xboole_0('#skF_6', C_151) | ~v3_pre_topc(C_151, '#skF_5') | k1_xboole_0=C_151 | ~m1_subset_1(C_151, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_165, c_405])).
% 16.08/7.07  tff(c_2472, plain, (![B_362]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_362, k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_3'('#skF_5', B_362, k2_struct_0('#skF_5')), '#skF_5') | '#skF_3'('#skF_5', B_362, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_362)=k2_struct_0('#skF_5') | ~m1_subset_1(B_362, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_2265, c_406])).
% 16.08/7.07  tff(c_10417, plain, (![B_710]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_710, k2_struct_0('#skF_5'))) | '#skF_3'('#skF_5', B_710, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_710)=k2_struct_0('#skF_5') | ~m1_subset_1(B_710, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1942, c_2472])).
% 16.08/7.07  tff(c_10421, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1830, c_10417])).
% 16.08/7.07  tff(c_10427, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_10421])).
% 16.08/7.07  tff(c_10428, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_800, c_10427])).
% 16.08/7.07  tff(c_10460, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10428, c_1942])).
% 16.08/7.07  tff(c_10491, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_10460])).
% 16.08/7.07  tff(c_10493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_800, c_785, c_10491])).
% 16.08/7.07  tff(c_10495, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_531])).
% 16.08/7.07  tff(c_10880, plain, (![A_738, B_739]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_738), B_739), A_738) | ~v4_pre_topc(B_739, A_738) | ~m1_subset_1(B_739, k1_zfmisc_1(u1_struct_0(A_738))) | ~l1_pre_topc(A_738))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_10891, plain, (![A_738]: (v3_pre_topc(k1_xboole_0, A_738) | ~v4_pre_topc(u1_struct_0(A_738), A_738) | ~m1_subset_1(u1_struct_0(A_738), k1_zfmisc_1(u1_struct_0(A_738))) | ~l1_pre_topc(A_738))), inference(superposition, [status(thm), theory('equality')], [c_375, c_10880])).
% 16.08/7.07  tff(c_10912, plain, (![A_741]: (v3_pre_topc(k1_xboole_0, A_741) | ~v4_pre_topc(u1_struct_0(A_741), A_741) | ~l1_pre_topc(A_741))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_10891])).
% 16.08/7.07  tff(c_10918, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_176, c_10912])).
% 16.08/7.07  tff(c_10921, plain, (v3_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_10495, c_10918])).
% 16.08/7.07  tff(c_26, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.08/7.07  tff(c_372, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k3_subset_1(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_363])).
% 16.08/7.07  tff(c_377, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_372])).
% 16.08/7.07  tff(c_10496, plain, (![B_711, A_712]: (v1_tops_1(B_711, A_712) | k2_pre_topc(A_712, B_711)!=k2_struct_0(A_712) | ~m1_subset_1(B_711, k1_zfmisc_1(u1_struct_0(A_712))) | ~l1_pre_topc(A_712))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.08/7.07  tff(c_10499, plain, (![B_711]: (v1_tops_1(B_711, '#skF_5') | k2_pre_topc('#skF_5', B_711)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_711, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_10496])).
% 16.08/7.07  tff(c_10781, plain, (![B_733]: (v1_tops_1(B_733, '#skF_5') | k2_pre_topc('#skF_5', B_733)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_733, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_10499])).
% 16.08/7.07  tff(c_10784, plain, (v1_tops_1('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_177, c_10781])).
% 16.08/7.07  tff(c_10795, plain, (k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_165, c_10784])).
% 16.08/7.07  tff(c_11140, plain, (![A_756, B_757, C_758]: (r2_hidden('#skF_2'(A_756, B_757, C_758), u1_struct_0(A_756)) | k2_pre_topc(A_756, B_757)=C_758 | ~m1_subset_1(C_758, k1_zfmisc_1(u1_struct_0(A_756))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0(A_756))) | ~l1_pre_topc(A_756))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_11151, plain, (![B_757, C_758]: (r2_hidden('#skF_2'('#skF_5', B_757, C_758), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_757)=C_758 | ~m1_subset_1(C_758, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_11140])).
% 16.08/7.07  tff(c_11156, plain, (![B_757, C_758]: (r2_hidden('#skF_2'('#skF_5', B_757, C_758), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_757)=C_758 | ~m1_subset_1(C_758, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_176, c_176, c_11151])).
% 16.08/7.07  tff(c_11766, plain, (![B_819, A_820, C_821]: (r1_xboole_0(B_819, '#skF_3'(A_820, B_819, C_821)) | ~r2_hidden('#skF_2'(A_820, B_819, C_821), C_821) | k2_pre_topc(A_820, B_819)=C_821 | ~m1_subset_1(C_821, k1_zfmisc_1(u1_struct_0(A_820))) | ~m1_subset_1(B_819, k1_zfmisc_1(u1_struct_0(A_820))) | ~l1_pre_topc(A_820))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_11779, plain, (![B_757]: (r1_xboole_0(B_757, '#skF_3'('#skF_5', B_757, k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_757)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_11156, c_11766])).
% 16.08/7.07  tff(c_11787, plain, (![B_757]: (r1_xboole_0(B_757, '#skF_3'('#skF_5', B_757, k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_757)=k2_struct_0('#skF_5') | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_11779])).
% 16.08/7.07  tff(c_11932, plain, (![A_830, B_831, C_832]: (v3_pre_topc('#skF_3'(A_830, B_831, C_832), A_830) | ~r2_hidden('#skF_2'(A_830, B_831, C_832), C_832) | k2_pre_topc(A_830, B_831)=C_832 | ~m1_subset_1(C_832, k1_zfmisc_1(u1_struct_0(A_830))) | ~m1_subset_1(B_831, k1_zfmisc_1(u1_struct_0(A_830))) | ~l1_pre_topc(A_830))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_11951, plain, (![B_757]: (v3_pre_topc('#skF_3'('#skF_5', B_757, k2_struct_0('#skF_5')), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_757)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_11156, c_11932])).
% 16.08/7.07  tff(c_11961, plain, (![B_757]: (v3_pre_topc('#skF_3'('#skF_5', B_757, k2_struct_0('#skF_5')), '#skF_5') | k2_pre_topc('#skF_5', B_757)=k2_struct_0('#skF_5') | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_11951])).
% 16.08/7.07  tff(c_12200, plain, (![A_860, B_861, C_862]: (m1_subset_1('#skF_3'(A_860, B_861, C_862), k1_zfmisc_1(u1_struct_0(A_860))) | ~r2_hidden('#skF_2'(A_860, B_861, C_862), C_862) | k2_pre_topc(A_860, B_861)=C_862 | ~m1_subset_1(C_862, k1_zfmisc_1(u1_struct_0(A_860))) | ~m1_subset_1(B_861, k1_zfmisc_1(u1_struct_0(A_860))) | ~l1_pre_topc(A_860))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_12216, plain, (![B_757]: (m1_subset_1('#skF_3'('#skF_5', B_757, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_757)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_757, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_11156, c_12200])).
% 16.08/7.07  tff(c_12229, plain, (![B_863]: (m1_subset_1('#skF_3'('#skF_5', B_863, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_863)=k2_struct_0('#skF_5') | ~m1_subset_1(B_863, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_96, c_176, c_119, c_176, c_176, c_12216])).
% 16.08/7.07  tff(c_12284, plain, (![B_868]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_868, k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_3'('#skF_5', B_868, k2_struct_0('#skF_5')), '#skF_5') | '#skF_3'('#skF_5', B_868, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_868)=k2_struct_0('#skF_5') | ~m1_subset_1(B_868, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_12229, c_406])).
% 16.08/7.07  tff(c_15632, plain, (![B_1063]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_1063, k2_struct_0('#skF_5'))) | '#skF_3'('#skF_5', B_1063, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_1063)=k2_struct_0('#skF_5') | ~m1_subset_1(B_1063, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_11961, c_12284])).
% 16.08/7.07  tff(c_15636, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_11787, c_15632])).
% 16.08/7.07  tff(c_15642, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_15636])).
% 16.08/7.07  tff(c_15643, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10795, c_15642])).
% 16.08/7.07  tff(c_36, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), '#skF_3'(A_26, B_70, C_92)) | ~r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_15658, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15643, c_36])).
% 16.08/7.07  tff(c_15677, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_177, c_176, c_119, c_176, c_15658])).
% 16.08/7.07  tff(c_15678, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_10795, c_15677])).
% 16.08/7.07  tff(c_15704, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_15678])).
% 16.08/7.07  tff(c_15713, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_11156, c_15704])).
% 16.08/7.07  tff(c_15718, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_119, c_15713])).
% 16.08/7.07  tff(c_15720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10795, c_15718])).
% 16.08/7.07  tff(c_15721, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_15678])).
% 16.08/7.07  tff(c_437, plain, (![A_187, C_188, B_189]: (m1_subset_1(A_187, C_188) | ~m1_subset_1(B_189, k1_zfmisc_1(C_188)) | ~r2_hidden(A_187, B_189))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.08/7.07  tff(c_446, plain, (![A_187, A_20]: (m1_subset_1(A_187, A_20) | ~r2_hidden(A_187, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_437])).
% 16.08/7.07  tff(c_15776, plain, (![A_1067]: (m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_1067))), inference(resolution, [status(thm)], [c_15721, c_446])).
% 16.08/7.07  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.08/7.07  tff(c_16146, plain, (![A_1075]: (k4_xboole_0(A_1075, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))=k3_subset_1(A_1075, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_15776, c_18])).
% 16.08/7.07  tff(c_14, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.08/7.07  tff(c_16181, plain, (k3_subset_1(k1_xboole_0, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16146, c_14])).
% 16.08/7.07  tff(c_22, plain, (![A_14, B_15]: (k3_subset_1(A_14, k3_subset_1(A_14, B_15))=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.08/7.07  tff(c_15888, plain, (![A_14]: (k3_subset_1(A_14, k3_subset_1(A_14, '#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))))='#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_15776, c_22])).
% 16.08/7.07  tff(c_16215, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k3_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16181, c_15888])).
% 16.08/7.07  tff(c_16223, plain, ('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_16215])).
% 16.08/7.07  tff(c_15771, plain, (![A_20]: (m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_20))), inference(resolution, [status(thm)], [c_15721, c_446])).
% 16.08/7.07  tff(c_16232, plain, (![A_20]: (m1_subset_1(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_16223, c_15771])).
% 16.08/7.07  tff(c_24, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.08/7.07  tff(c_15749, plain, (![A_16]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_16) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_15721, c_24])).
% 16.08/7.07  tff(c_15775, plain, (![A_16]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_15749])).
% 16.08/7.07  tff(c_16231, plain, (![A_16]: (r2_hidden(k1_xboole_0, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_16223, c_15775])).
% 16.08/7.07  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.08/7.07  tff(c_12029, plain, (![B_843, D_844, C_845, A_846]: (~r1_xboole_0(B_843, D_844) | ~r2_hidden(C_845, D_844) | ~v3_pre_topc(D_844, A_846) | ~m1_subset_1(D_844, k1_zfmisc_1(u1_struct_0(A_846))) | ~r2_hidden(C_845, k2_pre_topc(A_846, B_843)) | ~m1_subset_1(C_845, u1_struct_0(A_846)) | ~m1_subset_1(B_843, k1_zfmisc_1(u1_struct_0(A_846))) | ~l1_pre_topc(A_846))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_16538, plain, (![C_1081, B_1082, A_1083, A_1084]: (~r2_hidden(C_1081, B_1082) | ~v3_pre_topc(B_1082, A_1083) | ~m1_subset_1(B_1082, k1_zfmisc_1(u1_struct_0(A_1083))) | ~r2_hidden(C_1081, k2_pre_topc(A_1083, A_1084)) | ~m1_subset_1(C_1081, u1_struct_0(A_1083)) | ~m1_subset_1(A_1084, k1_zfmisc_1(u1_struct_0(A_1083))) | ~l1_pre_topc(A_1083) | k3_xboole_0(A_1084, B_1082)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_12029])).
% 16.08/7.07  tff(c_16540, plain, (![A_16, A_1083, A_1084]: (~v3_pre_topc(A_16, A_1083) | ~m1_subset_1(A_16, k1_zfmisc_1(u1_struct_0(A_1083))) | ~r2_hidden(k1_xboole_0, k2_pre_topc(A_1083, A_1084)) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_1083)) | ~m1_subset_1(A_1084, k1_zfmisc_1(u1_struct_0(A_1083))) | ~l1_pre_topc(A_1083) | k3_xboole_0(A_1084, A_16)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16231, c_16538])).
% 16.08/7.07  tff(c_16634, plain, (![A_1088, A_1089, A_1090]: (~v3_pre_topc(A_1088, A_1089) | ~m1_subset_1(A_1088, k1_zfmisc_1(u1_struct_0(A_1089))) | ~m1_subset_1(A_1090, k1_zfmisc_1(u1_struct_0(A_1089))) | ~l1_pre_topc(A_1089) | k3_xboole_0(A_1090, A_1088)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16232, c_16231, c_16540])).
% 16.08/7.07  tff(c_16637, plain, (![A_1089, A_1090]: (~v3_pre_topc(k1_xboole_0, A_1089) | ~m1_subset_1(A_1090, k1_zfmisc_1(u1_struct_0(A_1089))) | ~l1_pre_topc(A_1089) | k3_xboole_0(A_1090, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16232, c_16634])).
% 16.08/7.07  tff(c_16666, plain, (![A_1091, A_1092]: (~v3_pre_topc(k1_xboole_0, A_1091) | ~m1_subset_1(A_1092, k1_zfmisc_1(u1_struct_0(A_1091))) | ~l1_pre_topc(A_1091))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16637])).
% 16.08/7.07  tff(c_16700, plain, (![A_1093]: (~v3_pre_topc(k1_xboole_0, A_1093) | ~l1_pre_topc(A_1093))), inference(resolution, [status(thm)], [c_16232, c_16666])).
% 16.08/7.07  tff(c_16703, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10921, c_16700])).
% 16.08/7.07  tff(c_16707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_16703])).
% 16.08/7.07  tff(c_16708, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_104])).
% 16.08/7.07  tff(c_16791, plain, (![A_1106, B_1107]: (k4_xboole_0(A_1106, k4_xboole_0(A_1106, B_1107))=k3_xboole_0(A_1106, B_1107))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.08/7.07  tff(c_16820, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_16791])).
% 16.08/7.07  tff(c_16825, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16820])).
% 16.08/7.07  tff(c_16943, plain, (![A_1119, B_1120]: (k4_xboole_0(A_1119, B_1120)=k3_subset_1(A_1119, B_1120) | ~m1_subset_1(B_1120, k1_zfmisc_1(A_1119)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.08/7.07  tff(c_16952, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_subset_1(A_13, A_13))), inference(resolution, [status(thm)], [c_119, c_16943])).
% 16.08/7.07  tff(c_16959, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16825, c_16952])).
% 16.08/7.07  tff(c_16759, plain, (![A_1102, B_1103]: (k5_xboole_0(A_1102, k3_xboole_0(A_1102, B_1103))=k4_xboole_0(A_1102, B_1103))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.08/7.07  tff(c_16771, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_16759])).
% 16.08/7.07  tff(c_16774, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16771])).
% 16.08/7.07  tff(c_16709, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_104])).
% 16.08/7.07  tff(c_100, plain, (r1_xboole_0('#skF_6', '#skF_7') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_16710, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 16.08/7.07  tff(c_16712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16709, c_16710])).
% 16.08/7.07  tff(c_16713, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_100])).
% 16.08/7.07  tff(c_16737, plain, (![A_1098, B_1099]: (k3_xboole_0(A_1098, B_1099)=k1_xboole_0 | ~r1_xboole_0(A_1098, B_1099))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.08/7.07  tff(c_16745, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_16713, c_16737])).
% 16.08/7.07  tff(c_16768, plain, (k5_xboole_0('#skF_6', k1_xboole_0)=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16745, c_16759])).
% 16.08/7.07  tff(c_16785, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16774, c_16768])).
% 16.08/7.07  tff(c_16718, plain, (![A_1094]: (u1_struct_0(A_1094)=k2_struct_0(A_1094) | ~l1_struct_0(A_1094))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.08/7.07  tff(c_16725, plain, (![A_1095]: (u1_struct_0(A_1095)=k2_struct_0(A_1095) | ~l1_pre_topc(A_1095))), inference(resolution, [status(thm)], [c_66, c_16718])).
% 16.08/7.07  tff(c_16729, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_96, c_16725])).
% 16.08/7.07  tff(c_16731, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_16729, c_94])).
% 16.08/7.07  tff(c_17176, plain, (![A_1137, B_1138]: (k2_pre_topc(A_1137, B_1138)=k2_struct_0(A_1137) | ~v1_tops_1(B_1138, A_1137) | ~m1_subset_1(B_1138, k1_zfmisc_1(u1_struct_0(A_1137))) | ~l1_pre_topc(A_1137))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.08/7.07  tff(c_17179, plain, (![B_1138]: (k2_pre_topc('#skF_5', B_1138)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1138, '#skF_5') | ~m1_subset_1(B_1138, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17176])).
% 16.08/7.07  tff(c_24720, plain, (![B_1625]: (k2_pre_topc('#skF_5', B_1625)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1625, '#skF_5') | ~m1_subset_1(B_1625, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17179])).
% 16.08/7.07  tff(c_24723, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_24720])).
% 16.08/7.07  tff(c_24737, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_24723])).
% 16.08/7.07  tff(c_17159, plain, (![A_1134, B_1135]: (k2_pre_topc(A_1134, B_1135)=B_1135 | ~v4_pre_topc(B_1135, A_1134) | ~m1_subset_1(B_1135, k1_zfmisc_1(u1_struct_0(A_1134))) | ~l1_pre_topc(A_1134))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.08/7.07  tff(c_17162, plain, (![B_1135]: (k2_pre_topc('#skF_5', B_1135)=B_1135 | ~v4_pre_topc(B_1135, '#skF_5') | ~m1_subset_1(B_1135, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17159])).
% 16.08/7.07  tff(c_24405, plain, (![B_1600]: (k2_pre_topc('#skF_5', B_1600)=B_1600 | ~v4_pre_topc(B_1600, '#skF_5') | ~m1_subset_1(B_1600, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17162])).
% 16.08/7.07  tff(c_24420, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_24405])).
% 16.08/7.07  tff(c_24426, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_24420])).
% 16.08/7.07  tff(c_98, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_24672, plain, (![B_1621, A_1622]: (v4_pre_topc(B_1621, A_1622) | k2_pre_topc(A_1622, B_1621)!=B_1621 | ~v2_pre_topc(A_1622) | ~m1_subset_1(B_1621, k1_zfmisc_1(u1_struct_0(A_1622))) | ~l1_pre_topc(A_1622))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.08/7.07  tff(c_24675, plain, (![B_1621]: (v4_pre_topc(B_1621, '#skF_5') | k2_pre_topc('#skF_5', B_1621)!=B_1621 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_1621, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_24672])).
% 16.08/7.07  tff(c_24693, plain, (![B_1624]: (v4_pre_topc(B_1624, '#skF_5') | k2_pre_topc('#skF_5', B_1624)!=B_1624 | ~m1_subset_1(B_1624, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_98, c_24675])).
% 16.08/7.07  tff(c_24696, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_16731, c_24693])).
% 16.08/7.07  tff(c_24710, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24426, c_24696])).
% 16.08/7.07  tff(c_24744, plain, (k2_struct_0('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24737, c_24710])).
% 16.08/7.07  tff(c_29610, plain, (![A_1947, B_1948, C_1949]: (r2_hidden('#skF_2'(A_1947, B_1948, C_1949), u1_struct_0(A_1947)) | k2_pre_topc(A_1947, B_1948)=C_1949 | ~m1_subset_1(C_1949, k1_zfmisc_1(u1_struct_0(A_1947))) | ~m1_subset_1(B_1948, k1_zfmisc_1(u1_struct_0(A_1947))) | ~l1_pre_topc(A_1947))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_29618, plain, (![B_1948, C_1949]: (r2_hidden('#skF_2'('#skF_5', B_1948, C_1949), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1948)=C_1949 | ~m1_subset_1(C_1949, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1948, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_29610])).
% 16.08/7.07  tff(c_29976, plain, (![B_1968, C_1969]: (r2_hidden('#skF_2'('#skF_5', B_1968, C_1969), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1968)=C_1969 | ~m1_subset_1(C_1969, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1968, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_29618])).
% 16.08/7.07  tff(c_16845, plain, (![A_1109, C_1110, B_1111]: (m1_subset_1(A_1109, C_1110) | ~m1_subset_1(B_1111, k1_zfmisc_1(C_1110)) | ~r2_hidden(A_1109, B_1111))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.08/7.07  tff(c_16856, plain, (![A_1109, A_13]: (m1_subset_1(A_1109, A_13) | ~r2_hidden(A_1109, A_13))), inference(resolution, [status(thm)], [c_119, c_16845])).
% 16.08/7.07  tff(c_29987, plain, (![B_1968, C_1969]: (m1_subset_1('#skF_2'('#skF_5', B_1968, C_1969), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1968)=C_1969 | ~m1_subset_1(C_1969, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1968, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_29976, c_16856])).
% 16.08/7.07  tff(c_16801, plain, (![B_1107]: (k3_xboole_0(k1_xboole_0, B_1107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16791, c_14])).
% 16.08/7.07  tff(c_88, plain, (![A_140]: (v3_pre_topc(k2_struct_0(A_140), A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_154])).
% 16.08/7.07  tff(c_24425, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_26, c_24405])).
% 16.08/7.07  tff(c_24443, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_24425])).
% 16.08/7.07  tff(c_16955, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=k3_subset_1(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_16943])).
% 16.08/7.07  tff(c_16961, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16955])).
% 16.08/7.07  tff(c_24542, plain, (![B_1611, A_1612]: (v4_pre_topc(B_1611, A_1612) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1612), B_1611), A_1612) | ~m1_subset_1(B_1611, k1_zfmisc_1(u1_struct_0(A_1612))) | ~l1_pre_topc(A_1612))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_24549, plain, (![A_1612]: (v4_pre_topc(k1_xboole_0, A_1612) | ~v3_pre_topc(u1_struct_0(A_1612), A_1612) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1612))) | ~l1_pre_topc(A_1612))), inference(superposition, [status(thm), theory('equality')], [c_16961, c_24542])).
% 16.08/7.07  tff(c_24594, plain, (![A_1614]: (v4_pre_topc(k1_xboole_0, A_1614) | ~v3_pre_topc(u1_struct_0(A_1614), A_1614) | ~l1_pre_topc(A_1614))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24549])).
% 16.08/7.07  tff(c_24600, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_24594])).
% 16.08/7.07  tff(c_24603, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_24600])).
% 16.08/7.07  tff(c_24604, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24443, c_24603])).
% 16.08/7.07  tff(c_24607, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_88, c_24604])).
% 16.08/7.07  tff(c_24611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_24607])).
% 16.08/7.07  tff(c_24612, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_24425])).
% 16.08/7.07  tff(c_106, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_16724, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_106])).
% 16.08/7.07  tff(c_16730, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_16729, c_16724])).
% 16.08/7.07  tff(c_16855, plain, (![A_1109]: (m1_subset_1(A_1109, k2_struct_0('#skF_5')) | ~r2_hidden(A_1109, '#skF_7'))), inference(resolution, [status(thm)], [c_16730, c_16845])).
% 16.08/7.07  tff(c_24843, plain, (![A_1632, C_1633, B_1634]: (~v2_struct_0(A_1632) | ~r2_hidden(C_1633, k2_pre_topc(A_1632, B_1634)) | ~m1_subset_1(C_1633, u1_struct_0(A_1632)) | ~m1_subset_1(B_1634, k1_zfmisc_1(u1_struct_0(A_1632))) | ~l1_pre_topc(A_1632))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_24849, plain, (![C_1633]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1633, k1_xboole_0) | ~m1_subset_1(C_1633, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24612, c_24843])).
% 16.08/7.07  tff(c_24857, plain, (![C_1633]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1633, k1_xboole_0) | ~m1_subset_1(C_1633, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_26, c_16729, c_16729, c_24849])).
% 16.08/7.07  tff(c_24860, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_24857])).
% 16.08/7.07  tff(c_78, plain, (![A_115, B_127, C_133]: (m1_subset_1('#skF_4'(A_115, B_127, C_133), k1_zfmisc_1(u1_struct_0(A_115))) | r2_hidden(C_133, k2_pre_topc(A_115, B_127)) | v2_struct_0(A_115) | ~m1_subset_1(C_133, u1_struct_0(A_115)) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_25285, plain, (![C_1653, A_1654, B_1655]: (r2_hidden(C_1653, '#skF_4'(A_1654, B_1655, C_1653)) | r2_hidden(C_1653, k2_pre_topc(A_1654, B_1655)) | v2_struct_0(A_1654) | ~m1_subset_1(C_1653, u1_struct_0(A_1654)) | ~m1_subset_1(B_1655, k1_zfmisc_1(u1_struct_0(A_1654))) | ~l1_pre_topc(A_1654))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_25287, plain, (![C_1653, B_1655]: (r2_hidden(C_1653, '#skF_4'('#skF_5', B_1655, C_1653)) | r2_hidden(C_1653, k2_pre_topc('#skF_5', B_1655)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1653, u1_struct_0('#skF_5')) | ~m1_subset_1(B_1655, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_25285])).
% 16.08/7.07  tff(c_25295, plain, (![C_1653, B_1655]: (r2_hidden(C_1653, '#skF_4'('#skF_5', B_1655, C_1653)) | r2_hidden(C_1653, k2_pre_topc('#skF_5', B_1655)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1653, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1655, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_25287])).
% 16.08/7.07  tff(c_25590, plain, (![C_1703, B_1704]: (r2_hidden(C_1703, '#skF_4'('#skF_5', B_1704, C_1703)) | r2_hidden(C_1703, k2_pre_topc('#skF_5', B_1704)) | ~m1_subset_1(C_1703, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1704, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_24860, c_25295])).
% 16.08/7.07  tff(c_25592, plain, (![C_1703]: (r2_hidden(C_1703, '#skF_4'('#skF_5', '#skF_6', C_1703)) | r2_hidden(C_1703, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1703, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16731, c_25590])).
% 16.08/7.07  tff(c_25608, plain, (![C_1705]: (r2_hidden(C_1705, '#skF_4'('#skF_5', '#skF_6', C_1705)) | r2_hidden(C_1705, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1705, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_24737, c_25592])).
% 16.08/7.07  tff(c_25810, plain, (![C_1723, A_1724]: (r2_hidden(C_1723, A_1724) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_1723), k1_zfmisc_1(A_1724)) | r2_hidden(C_1723, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1723, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_25608, c_24])).
% 16.08/7.07  tff(c_25814, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_78, c_25810])).
% 16.08/7.07  tff(c_25821, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16731, c_16729, c_16729, c_24737, c_16729, c_25814])).
% 16.08/7.07  tff(c_25822, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_24860, c_25821])).
% 16.08/7.07  tff(c_102, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_184])).
% 16.08/7.07  tff(c_16717, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_102])).
% 16.08/7.07  tff(c_25873, plain, (![B_1732, D_1733, C_1734, A_1735]: (~r1_xboole_0(B_1732, D_1733) | ~r2_hidden(C_1734, D_1733) | ~v3_pre_topc(D_1733, A_1735) | ~m1_subset_1(D_1733, k1_zfmisc_1(u1_struct_0(A_1735))) | ~r2_hidden(C_1734, k2_pre_topc(A_1735, B_1732)) | ~m1_subset_1(C_1734, u1_struct_0(A_1735)) | ~m1_subset_1(B_1732, k1_zfmisc_1(u1_struct_0(A_1735))) | ~l1_pre_topc(A_1735))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_25937, plain, (![C_1739, A_1740]: (~r2_hidden(C_1739, '#skF_7') | ~v3_pre_topc('#skF_7', A_1740) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_1740))) | ~r2_hidden(C_1739, k2_pre_topc(A_1740, '#skF_6')) | ~m1_subset_1(C_1739, u1_struct_0(A_1740)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1740))) | ~l1_pre_topc(A_1740))), inference(resolution, [status(thm)], [c_16713, c_25873])).
% 16.08/7.07  tff(c_25939, plain, (![C_1739]: (~r2_hidden(C_1739, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_1739, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1739, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_25937])).
% 16.08/7.07  tff(c_25942, plain, (![C_1741]: (~r2_hidden(C_1741, '#skF_7') | ~r2_hidden(C_1741, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1741, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16731, c_16729, c_16729, c_24737, c_16730, c_16717, c_25939])).
% 16.08/7.07  tff(c_25951, plain, (![C_1742]: (~r2_hidden(C_1742, '#skF_7') | ~m1_subset_1(C_1742, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_25822, c_25942])).
% 16.08/7.07  tff(c_25959, plain, (![A_1109]: (~r2_hidden(A_1109, '#skF_7'))), inference(resolution, [status(thm)], [c_16855, c_25951])).
% 16.08/7.07  tff(c_24613, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_24425])).
% 16.08/7.07  tff(c_24625, plain, (![A_1615, B_1616]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_1615), B_1616), A_1615) | ~v4_pre_topc(B_1616, A_1615) | ~m1_subset_1(B_1616, k1_zfmisc_1(u1_struct_0(A_1615))) | ~l1_pre_topc(A_1615))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_24629, plain, (![A_1615]: (v3_pre_topc(u1_struct_0(A_1615), A_1615) | ~v4_pre_topc(k1_xboole_0, A_1615) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1615))) | ~l1_pre_topc(A_1615))), inference(superposition, [status(thm), theory('equality')], [c_16961, c_24625])).
% 16.08/7.07  tff(c_24644, plain, (![A_1617]: (v3_pre_topc(u1_struct_0(A_1617), A_1617) | ~v4_pre_topc(k1_xboole_0, A_1617) | ~l1_pre_topc(A_1617))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24629])).
% 16.08/7.07  tff(c_24647, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_24644])).
% 16.08/7.07  tff(c_24649, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_24613, c_24647])).
% 16.08/7.07  tff(c_32, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), u1_struct_0(A_26)) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_28008, plain, (![A_1870, B_1871, C_1872, E_1873]: (r2_hidden('#skF_2'(A_1870, B_1871, C_1872), C_1872) | ~r1_xboole_0(B_1871, E_1873) | ~r2_hidden('#skF_2'(A_1870, B_1871, C_1872), E_1873) | ~v3_pre_topc(E_1873, A_1870) | ~m1_subset_1(E_1873, k1_zfmisc_1(u1_struct_0(A_1870))) | k2_pre_topc(A_1870, B_1871)=C_1872 | ~m1_subset_1(C_1872, k1_zfmisc_1(u1_struct_0(A_1870))) | ~m1_subset_1(B_1871, k1_zfmisc_1(u1_struct_0(A_1870))) | ~l1_pre_topc(A_1870))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_28062, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_32, c_28008])).
% 16.08/7.07  tff(c_29473, plain, (![A_1936, B_1937, C_1938]: (r2_hidden('#skF_2'(A_1936, B_1937, C_1938), C_1938) | ~r1_xboole_0(B_1937, u1_struct_0(A_1936)) | ~v3_pre_topc(u1_struct_0(A_1936), A_1936) | k2_pre_topc(A_1936, B_1937)=C_1938 | ~m1_subset_1(C_1938, k1_zfmisc_1(u1_struct_0(A_1936))) | ~m1_subset_1(B_1937, k1_zfmisc_1(u1_struct_0(A_1936))) | ~l1_pre_topc(A_1936))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_28062])).
% 16.08/7.07  tff(c_29477, plain, (![B_1937, C_1938]: (r2_hidden('#skF_2'('#skF_5', B_1937, C_1938), C_1938) | ~r1_xboole_0(B_1937, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_1937)=C_1938 | ~m1_subset_1(C_1938, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1937, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_29473])).
% 16.08/7.07  tff(c_29512, plain, (![B_1942, C_1943]: (r2_hidden('#skF_2'('#skF_5', B_1942, C_1943), C_1943) | ~r1_xboole_0(B_1942, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1942)=C_1943 | ~m1_subset_1(C_1943, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1942, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_24649, c_16729, c_29477])).
% 16.08/7.07  tff(c_29527, plain, (![B_1942]: (r2_hidden('#skF_2'('#skF_5', B_1942, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_1942, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1942)='#skF_7' | ~m1_subset_1(B_1942, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_16730, c_29512])).
% 16.08/7.07  tff(c_29545, plain, (![B_1944]: (~r1_xboole_0(B_1944, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1944)='#skF_7' | ~m1_subset_1(B_1944, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_25959, c_29527])).
% 16.08/7.07  tff(c_29575, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_26, c_29545])).
% 16.08/7.07  tff(c_29589, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_24612, c_29575])).
% 16.08/7.07  tff(c_29590, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_16708, c_29589])).
% 16.08/7.07  tff(c_29593, plain, (k3_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_29590])).
% 16.08/7.07  tff(c_29597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16801, c_29593])).
% 16.08/7.07  tff(c_29599, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_24857])).
% 16.08/7.07  tff(c_17193, plain, (![A_1140]: (k2_pre_topc(A_1140, u1_struct_0(A_1140))=u1_struct_0(A_1140) | ~v4_pre_topc(u1_struct_0(A_1140), A_1140) | ~l1_pre_topc(A_1140))), inference(resolution, [status(thm)], [c_119, c_17159])).
% 16.08/7.07  tff(c_17196, plain, (k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))=u1_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17193])).
% 16.08/7.07  tff(c_17198, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_17196])).
% 16.08/7.07  tff(c_17199, plain, (~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_17198])).
% 16.08/7.07  tff(c_17570, plain, (![B_1170]: (k2_pre_topc('#skF_5', B_1170)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1170, '#skF_5') | ~m1_subset_1(B_1170, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17179])).
% 16.08/7.07  tff(c_17573, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_17570])).
% 16.08/7.07  tff(c_17587, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_17573])).
% 16.08/7.07  tff(c_17208, plain, (![B_1142]: (k2_pre_topc('#skF_5', B_1142)=B_1142 | ~v4_pre_topc(B_1142, '#skF_5') | ~m1_subset_1(B_1142, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17162])).
% 16.08/7.07  tff(c_17223, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_17208])).
% 16.08/7.07  tff(c_17243, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_17223])).
% 16.08/7.07  tff(c_17475, plain, (![B_1162, A_1163]: (v4_pre_topc(B_1162, A_1163) | k2_pre_topc(A_1163, B_1162)!=B_1162 | ~v2_pre_topc(A_1163) | ~m1_subset_1(B_1162, k1_zfmisc_1(u1_struct_0(A_1163))) | ~l1_pre_topc(A_1163))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.08/7.07  tff(c_17478, plain, (![B_1162]: (v4_pre_topc(B_1162, '#skF_5') | k2_pre_topc('#skF_5', B_1162)!=B_1162 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_1162, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17475])).
% 16.08/7.07  tff(c_17496, plain, (![B_1165]: (v4_pre_topc(B_1165, '#skF_5') | k2_pre_topc('#skF_5', B_1165)!=B_1165 | ~m1_subset_1(B_1165, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_98, c_17478])).
% 16.08/7.07  tff(c_17499, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_16731, c_17496])).
% 16.08/7.07  tff(c_17513, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_17243, c_17499])).
% 16.08/7.07  tff(c_17602, plain, (k2_struct_0('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_17587, c_17513])).
% 16.08/7.07  tff(c_23221, plain, (![A_1518, B_1519, C_1520]: (r2_hidden('#skF_2'(A_1518, B_1519, C_1520), u1_struct_0(A_1518)) | k2_pre_topc(A_1518, B_1519)=C_1520 | ~m1_subset_1(C_1520, k1_zfmisc_1(u1_struct_0(A_1518))) | ~m1_subset_1(B_1519, k1_zfmisc_1(u1_struct_0(A_1518))) | ~l1_pre_topc(A_1518))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_23229, plain, (![B_1519, C_1520]: (r2_hidden('#skF_2'('#skF_5', B_1519, C_1520), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1519)=C_1520 | ~m1_subset_1(C_1520, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1519, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_23221])).
% 16.08/7.07  tff(c_23538, plain, (![B_1536, C_1537]: (r2_hidden('#skF_2'('#skF_5', B_1536, C_1537), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1536)=C_1537 | ~m1_subset_1(C_1537, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1536, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_23229])).
% 16.08/7.07  tff(c_23549, plain, (![B_1536, C_1537]: (m1_subset_1('#skF_2'('#skF_5', B_1536, C_1537), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1536)=C_1537 | ~m1_subset_1(C_1537, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1536, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_23538, c_16856])).
% 16.08/7.07  tff(c_17226, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_26, c_17208])).
% 16.08/7.07  tff(c_17244, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_17226])).
% 16.08/7.07  tff(c_17405, plain, (![B_1157, A_1158]: (v4_pre_topc(B_1157, A_1158) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1158), B_1157), A_1158) | ~m1_subset_1(B_1157, k1_zfmisc_1(u1_struct_0(A_1158))) | ~l1_pre_topc(A_1158))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_17412, plain, (![A_1158]: (v4_pre_topc(k1_xboole_0, A_1158) | ~v3_pre_topc(u1_struct_0(A_1158), A_1158) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1158))) | ~l1_pre_topc(A_1158))), inference(superposition, [status(thm), theory('equality')], [c_16961, c_17405])).
% 16.08/7.07  tff(c_17427, plain, (![A_1159]: (v4_pre_topc(k1_xboole_0, A_1159) | ~v3_pre_topc(u1_struct_0(A_1159), A_1159) | ~l1_pre_topc(A_1159))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_17412])).
% 16.08/7.07  tff(c_17433, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17427])).
% 16.08/7.07  tff(c_17436, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17433])).
% 16.08/7.07  tff(c_17437, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_17244, c_17436])).
% 16.08/7.07  tff(c_17440, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_88, c_17437])).
% 16.08/7.07  tff(c_17444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_17440])).
% 16.08/7.07  tff(c_17445, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_17226])).
% 16.08/7.07  tff(c_17446, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_17226])).
% 16.08/7.07  tff(c_17546, plain, (![A_1167, B_1168]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_1167), B_1168), A_1167) | ~v4_pre_topc(B_1168, A_1167) | ~m1_subset_1(B_1168, k1_zfmisc_1(u1_struct_0(A_1167))) | ~l1_pre_topc(A_1167))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.08/7.07  tff(c_17550, plain, (![A_1167]: (v3_pre_topc(u1_struct_0(A_1167), A_1167) | ~v4_pre_topc(k1_xboole_0, A_1167) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1167))) | ~l1_pre_topc(A_1167))), inference(superposition, [status(thm), theory('equality')], [c_16961, c_17546])).
% 16.08/7.07  tff(c_17564, plain, (![A_1169]: (v3_pre_topc(u1_struct_0(A_1169), A_1169) | ~v4_pre_topc(k1_xboole_0, A_1169) | ~l1_pre_topc(A_1169))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_17550])).
% 16.08/7.07  tff(c_17567, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17564])).
% 16.08/7.07  tff(c_17569, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17446, c_17567])).
% 16.08/7.07  tff(c_20214, plain, (![A_1380, B_1381, C_1382, E_1383]: (v3_pre_topc('#skF_3'(A_1380, B_1381, C_1382), A_1380) | ~r1_xboole_0(B_1381, E_1383) | ~r2_hidden('#skF_2'(A_1380, B_1381, C_1382), E_1383) | ~v3_pre_topc(E_1383, A_1380) | ~m1_subset_1(E_1383, k1_zfmisc_1(u1_struct_0(A_1380))) | k2_pre_topc(A_1380, B_1381)=C_1382 | ~m1_subset_1(C_1382, k1_zfmisc_1(u1_struct_0(A_1380))) | ~m1_subset_1(B_1381, k1_zfmisc_1(u1_struct_0(A_1380))) | ~l1_pre_topc(A_1380))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_20267, plain, (![A_26, B_70, C_92]: (v3_pre_topc('#skF_3'(A_26, B_70, C_92), A_26) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_32, c_20214])).
% 16.08/7.07  tff(c_22620, plain, (![A_1490, B_1491, C_1492]: (v3_pre_topc('#skF_3'(A_1490, B_1491, C_1492), A_1490) | ~r1_xboole_0(B_1491, u1_struct_0(A_1490)) | ~v3_pre_topc(u1_struct_0(A_1490), A_1490) | k2_pre_topc(A_1490, B_1491)=C_1492 | ~m1_subset_1(C_1492, k1_zfmisc_1(u1_struct_0(A_1490))) | ~m1_subset_1(B_1491, k1_zfmisc_1(u1_struct_0(A_1490))) | ~l1_pre_topc(A_1490))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_20267])).
% 16.08/7.07  tff(c_22624, plain, (![B_1491, C_1492]: (v3_pre_topc('#skF_3'('#skF_5', B_1491, C_1492), '#skF_5') | ~r1_xboole_0(B_1491, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_1491)=C_1492 | ~m1_subset_1(C_1492, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1491, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_22620])).
% 16.08/7.07  tff(c_22631, plain, (![B_1493, C_1494]: (v3_pre_topc('#skF_3'('#skF_5', B_1493, C_1494), '#skF_5') | ~r1_xboole_0(B_1493, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1493)=C_1494 | ~m1_subset_1(C_1494, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1493, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_17569, c_16729, c_22624])).
% 16.08/7.07  tff(c_22662, plain, (![B_1495]: (v3_pre_topc('#skF_3'('#skF_5', B_1495, '#skF_6'), '#skF_5') | ~r1_xboole_0(B_1495, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1495)='#skF_6' | ~m1_subset_1(B_1495, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_16731, c_22631])).
% 16.08/7.07  tff(c_22692, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_6'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_26, c_22662])).
% 16.08/7.07  tff(c_22704, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_6'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_17445, c_22692])).
% 16.08/7.07  tff(c_22710, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_22704])).
% 16.08/7.07  tff(c_22721, plain, (k3_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_22710])).
% 16.08/7.07  tff(c_22725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16801, c_22721])).
% 16.08/7.07  tff(c_22727, plain, (r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_22704])).
% 16.08/7.07  tff(c_17803, plain, (![A_1183, C_1184, B_1185]: (~v2_struct_0(A_1183) | ~r2_hidden(C_1184, k2_pre_topc(A_1183, B_1185)) | ~m1_subset_1(C_1184, u1_struct_0(A_1183)) | ~m1_subset_1(B_1185, k1_zfmisc_1(u1_struct_0(A_1183))) | ~l1_pre_topc(A_1183))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_17809, plain, (![C_1184]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1184, k1_xboole_0) | ~m1_subset_1(C_1184, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17445, c_17803])).
% 16.08/7.07  tff(c_17815, plain, (![C_1184]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1184, k1_xboole_0) | ~m1_subset_1(C_1184, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_26, c_16729, c_16729, c_17809])).
% 16.08/7.07  tff(c_17816, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_17815])).
% 16.08/7.07  tff(c_18174, plain, (![C_1207, A_1208, B_1209]: (r2_hidden(C_1207, '#skF_4'(A_1208, B_1209, C_1207)) | r2_hidden(C_1207, k2_pre_topc(A_1208, B_1209)) | v2_struct_0(A_1208) | ~m1_subset_1(C_1207, u1_struct_0(A_1208)) | ~m1_subset_1(B_1209, k1_zfmisc_1(u1_struct_0(A_1208))) | ~l1_pre_topc(A_1208))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_18176, plain, (![C_1207, B_1209]: (r2_hidden(C_1207, '#skF_4'('#skF_5', B_1209, C_1207)) | r2_hidden(C_1207, k2_pre_topc('#skF_5', B_1209)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1207, u1_struct_0('#skF_5')) | ~m1_subset_1(B_1209, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_18174])).
% 16.08/7.07  tff(c_18184, plain, (![C_1207, B_1209]: (r2_hidden(C_1207, '#skF_4'('#skF_5', B_1209, C_1207)) | r2_hidden(C_1207, k2_pre_topc('#skF_5', B_1209)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1207, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1209, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_18176])).
% 16.08/7.07  tff(c_18454, plain, (![C_1248, B_1249]: (r2_hidden(C_1248, '#skF_4'('#skF_5', B_1249, C_1248)) | r2_hidden(C_1248, k2_pre_topc('#skF_5', B_1249)) | ~m1_subset_1(C_1248, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1249, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_17816, c_18184])).
% 16.08/7.07  tff(c_18456, plain, (![C_1248]: (r2_hidden(C_1248, '#skF_4'('#skF_5', '#skF_6', C_1248)) | r2_hidden(C_1248, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1248, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16731, c_18454])).
% 16.08/7.07  tff(c_18471, plain, (![C_1250]: (r2_hidden(C_1250, '#skF_4'('#skF_5', '#skF_6', C_1250)) | r2_hidden(C_1250, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1250, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_17587, c_18456])).
% 16.08/7.07  tff(c_18658, plain, (![C_1268, A_1269]: (r2_hidden(C_1268, A_1269) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_1268), k1_zfmisc_1(A_1269)) | r2_hidden(C_1268, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1268, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18471, c_24])).
% 16.08/7.07  tff(c_18662, plain, (![C_133]: (r2_hidden(C_133, u1_struct_0('#skF_5')) | r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')) | r2_hidden(C_133, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_78, c_18658])).
% 16.08/7.07  tff(c_18669, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16731, c_16729, c_16729, c_17587, c_16729, c_18662])).
% 16.08/7.07  tff(c_18670, plain, (![C_133]: (r2_hidden(C_133, k2_struct_0('#skF_5')) | ~m1_subset_1(C_133, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_17816, c_18669])).
% 16.08/7.07  tff(c_18823, plain, (![B_1277, D_1278, C_1279, A_1280]: (~r1_xboole_0(B_1277, D_1278) | ~r2_hidden(C_1279, D_1278) | ~v3_pre_topc(D_1278, A_1280) | ~m1_subset_1(D_1278, k1_zfmisc_1(u1_struct_0(A_1280))) | ~r2_hidden(C_1279, k2_pre_topc(A_1280, B_1277)) | ~m1_subset_1(C_1279, u1_struct_0(A_1280)) | ~m1_subset_1(B_1277, k1_zfmisc_1(u1_struct_0(A_1280))) | ~l1_pre_topc(A_1280))), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.08/7.07  tff(c_18868, plain, (![C_1285, A_1286]: (~r2_hidden(C_1285, '#skF_7') | ~v3_pre_topc('#skF_7', A_1286) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_1286))) | ~r2_hidden(C_1285, k2_pre_topc(A_1286, '#skF_6')) | ~m1_subset_1(C_1285, u1_struct_0(A_1286)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1286))) | ~l1_pre_topc(A_1286))), inference(resolution, [status(thm)], [c_16713, c_18823])).
% 16.08/7.07  tff(c_18870, plain, (![C_1285]: (~r2_hidden(C_1285, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_1285, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1285, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_18868])).
% 16.08/7.07  tff(c_18873, plain, (![C_1287]: (~r2_hidden(C_1287, '#skF_7') | ~r2_hidden(C_1287, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1287, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16731, c_16729, c_16729, c_17587, c_16730, c_16717, c_18870])).
% 16.08/7.07  tff(c_18882, plain, (![C_1288]: (~r2_hidden(C_1288, '#skF_7') | ~m1_subset_1(C_1288, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18670, c_18873])).
% 16.08/7.07  tff(c_18890, plain, (![A_1109]: (~r2_hidden(A_1109, '#skF_7'))), inference(resolution, [status(thm)], [c_16855, c_18882])).
% 16.08/7.07  tff(c_20893, plain, (![A_1398, B_1399, C_1400, E_1401]: (r2_hidden('#skF_2'(A_1398, B_1399, C_1400), C_1400) | ~r1_xboole_0(B_1399, E_1401) | ~r2_hidden('#skF_2'(A_1398, B_1399, C_1400), E_1401) | ~v3_pre_topc(E_1401, A_1398) | ~m1_subset_1(E_1401, k1_zfmisc_1(u1_struct_0(A_1398))) | k2_pre_topc(A_1398, B_1399)=C_1400 | ~m1_subset_1(C_1400, k1_zfmisc_1(u1_struct_0(A_1398))) | ~m1_subset_1(B_1399, k1_zfmisc_1(u1_struct_0(A_1398))) | ~l1_pre_topc(A_1398))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.08/7.07  tff(c_20949, plain, (![A_26, B_70, C_92]: (r2_hidden('#skF_2'(A_26, B_70, C_92), C_92) | ~r1_xboole_0(B_70, u1_struct_0(A_26)) | ~v3_pre_topc(u1_struct_0(A_26), A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | k2_pre_topc(A_26, B_70)=C_92 | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_32, c_20893])).
% 16.08/7.07  tff(c_23035, plain, (![A_1507, B_1508, C_1509]: (r2_hidden('#skF_2'(A_1507, B_1508, C_1509), C_1509) | ~r1_xboole_0(B_1508, u1_struct_0(A_1507)) | ~v3_pre_topc(u1_struct_0(A_1507), A_1507) | k2_pre_topc(A_1507, B_1508)=C_1509 | ~m1_subset_1(C_1509, k1_zfmisc_1(u1_struct_0(A_1507))) | ~m1_subset_1(B_1508, k1_zfmisc_1(u1_struct_0(A_1507))) | ~l1_pre_topc(A_1507))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_20949])).
% 16.08/7.07  tff(c_23039, plain, (![B_1508, C_1509]: (r2_hidden('#skF_2'('#skF_5', B_1508, C_1509), C_1509) | ~r1_xboole_0(B_1508, u1_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', B_1508)=C_1509 | ~m1_subset_1(C_1509, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1508, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_23035])).
% 16.08/7.07  tff(c_23129, plain, (![B_1512, C_1513]: (r2_hidden('#skF_2'('#skF_5', B_1512, C_1513), C_1513) | ~r1_xboole_0(B_1512, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1512)=C_1513 | ~m1_subset_1(C_1513, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1512, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_16729, c_17569, c_16729, c_23039])).
% 16.08/7.07  tff(c_23144, plain, (![B_1512]: (r2_hidden('#skF_2'('#skF_5', B_1512, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_1512, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1512)='#skF_7' | ~m1_subset_1(B_1512, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_16730, c_23129])).
% 16.08/7.07  tff(c_23162, plain, (![B_1514]: (~r1_xboole_0(B_1514, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1514)='#skF_7' | ~m1_subset_1(B_1514, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_18890, c_23144])).
% 16.08/7.07  tff(c_23192, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_26, c_23162])).
% 16.08/7.07  tff(c_23205, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_17445, c_22727, c_23192])).
% 16.08/7.07  tff(c_23207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16708, c_23205])).
% 16.08/7.07  tff(c_23209, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_17815])).
% 16.08/7.07  tff(c_17807, plain, (![C_1184]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1184, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1184, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17587, c_17803])).
% 16.08/7.07  tff(c_17813, plain, (![C_1184]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1184, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1184, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16731, c_16729, c_16729, c_17807])).
% 16.08/7.07  tff(c_23235, plain, (![C_1184]: (~r2_hidden(C_1184, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1184, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_23209, c_17813])).
% 16.08/7.07  tff(c_24086, plain, (![B_1578, C_1579]: (~m1_subset_1('#skF_2'('#skF_5', B_1578, C_1579), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1578)=C_1579 | ~m1_subset_1(C_1579, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1578, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_23538, c_23235])).
% 16.08/7.07  tff(c_24099, plain, (![B_1580, C_1581]: (k2_pre_topc('#skF_5', B_1580)=C_1581 | ~m1_subset_1(C_1581, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1580, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_23549, c_24086])).
% 16.08/7.07  tff(c_24114, plain, (![B_1582]: (k2_pre_topc('#skF_5', B_1582)='#skF_6' | ~m1_subset_1(B_1582, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_16731, c_24099])).
% 16.08/7.07  tff(c_24129, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_16731, c_24114])).
% 16.08/7.07  tff(c_24133, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24129, c_17587])).
% 16.08/7.07  tff(c_24135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17602, c_24133])).
% 16.08/7.07  tff(c_24136, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_17223])).
% 16.08/7.07  tff(c_24219, plain, (![B_1589]: (k2_pre_topc('#skF_5', B_1589)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1589, '#skF_5') | ~m1_subset_1(B_1589, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17179])).
% 16.08/7.07  tff(c_24222, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_24219])).
% 16.08/7.07  tff(c_24236, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_24136, c_24222])).
% 16.08/7.07  tff(c_17201, plain, (![A_1141]: (k2_pre_topc(A_1141, u1_struct_0(A_1141))=k2_struct_0(A_1141) | ~v1_tops_1(u1_struct_0(A_1141), A_1141) | ~l1_pre_topc(A_1141))), inference(resolution, [status(thm)], [c_119, c_17176])).
% 16.08/7.07  tff(c_17204, plain, (k2_pre_topc('#skF_5', u1_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17201])).
% 16.08/7.07  tff(c_17206, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5') | ~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16729, c_17204])).
% 16.08/7.07  tff(c_17207, plain, (~v1_tops_1(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_17206])).
% 16.08/7.07  tff(c_17227, plain, (![B_1143, A_1144]: (v1_tops_1(B_1143, A_1144) | k2_pre_topc(A_1144, B_1143)!=k2_struct_0(A_1144) | ~m1_subset_1(B_1143, k1_zfmisc_1(u1_struct_0(A_1144))) | ~l1_pre_topc(A_1144))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.08/7.07  tff(c_17230, plain, (![B_1143]: (v1_tops_1(B_1143, '#skF_5') | k2_pre_topc('#skF_5', B_1143)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1143, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_17227])).
% 16.08/7.07  tff(c_24162, plain, (![B_1585]: (v1_tops_1(B_1585, '#skF_5') | k2_pre_topc('#skF_5', B_1585)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_1585, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17230])).
% 16.08/7.07  tff(c_24172, plain, (v1_tops_1(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_119, c_24162])).
% 16.08/7.07  tff(c_24182, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_17207, c_24172])).
% 16.08/7.07  tff(c_24248, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24236, c_24236, c_24182])).
% 16.08/7.07  tff(c_24266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24136, c_24248])).
% 16.08/7.07  tff(c_24267, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_17206])).
% 16.08/7.07  tff(c_24350, plain, (![B_1596, A_1597]: (v4_pre_topc(B_1596, A_1597) | k2_pre_topc(A_1597, B_1596)!=B_1596 | ~v2_pre_topc(A_1597) | ~m1_subset_1(B_1596, k1_zfmisc_1(u1_struct_0(A_1597))) | ~l1_pre_topc(A_1597))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.08/7.07  tff(c_24353, plain, (![B_1596]: (v4_pre_topc(B_1596, '#skF_5') | k2_pre_topc('#skF_5', B_1596)!=B_1596 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_1596, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16729, c_24350])).
% 16.08/7.07  tff(c_24367, plain, (![B_1598]: (v4_pre_topc(B_1598, '#skF_5') | k2_pre_topc('#skF_5', B_1598)!=B_1598 | ~m1_subset_1(B_1598, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_98, c_24353])).
% 16.08/7.07  tff(c_24377, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_119, c_24367])).
% 16.08/7.07  tff(c_24390, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24267, c_24377])).
% 16.08/7.07  tff(c_24392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17199, c_24390])).
% 16.08/7.07  tff(c_24393, plain, (k2_pre_topc('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_17198])).
% 16.08/7.07  tff(c_24851, plain, (![C_1633]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1633, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1633, u1_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24393, c_24843])).
% 16.08/7.07  tff(c_24859, plain, (![C_1633]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1633, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1633, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_119, c_16729, c_16729, c_24851])).
% 16.08/7.07  tff(c_29625, plain, (![C_1633]: (~r2_hidden(C_1633, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1633, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_29599, c_24859])).
% 16.08/7.07  tff(c_30623, plain, (![B_2011, C_2012]: (~m1_subset_1('#skF_2'('#skF_5', B_2011, C_2012), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_2011)=C_2012 | ~m1_subset_1(C_2012, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2011, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_29976, c_29625])).
% 16.08/7.07  tff(c_30636, plain, (![B_2013, C_2014]: (k2_pre_topc('#skF_5', B_2013)=C_2014 | ~m1_subset_1(C_2014, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_2013, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_29987, c_30623])).
% 16.08/7.07  tff(c_30651, plain, (![B_2015]: (k2_pre_topc('#skF_5', B_2015)='#skF_6' | ~m1_subset_1(B_2015, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_16731, c_30636])).
% 16.08/7.07  tff(c_30666, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_16731, c_30651])).
% 16.08/7.07  tff(c_30670, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30666, c_24737])).
% 16.08/7.07  tff(c_30672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24744, c_30670])).
% 16.08/7.07  tff(c_30673, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_24420])).
% 16.08/7.07  tff(c_30713, plain, (![B_2020]: (k2_pre_topc('#skF_5', B_2020)=k2_struct_0('#skF_5') | ~v1_tops_1(B_2020, '#skF_5') | ~m1_subset_1(B_2020, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17179])).
% 16.08/7.07  tff(c_30716, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_16731, c_30713])).
% 16.08/7.07  tff(c_30730, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16709, c_30673, c_30716])).
% 16.08/7.07  tff(c_16957, plain, (k4_xboole_0(k2_struct_0('#skF_5'), '#skF_7')=k3_subset_1(k2_struct_0('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_16730, c_16943])).
% 16.08/7.07  tff(c_30764, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30730, c_30730, c_16957])).
% 16.08/7.07  tff(c_30777, plain, (k3_subset_1('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16785, c_30764])).
% 16.08/7.07  tff(c_17005, plain, (![A_1125, B_1126]: (k3_subset_1(A_1125, k3_subset_1(A_1125, B_1126))=B_1126 | ~m1_subset_1(B_1126, k1_zfmisc_1(A_1125)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.08/7.07  tff(c_17015, plain, (k3_subset_1(k2_struct_0('#skF_5'), k3_subset_1(k2_struct_0('#skF_5'), '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_16730, c_17005])).
% 16.08/7.07  tff(c_30761, plain, (k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_30730, c_30730, c_17015])).
% 16.08/7.07  tff(c_30845, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16959, c_30777, c_30761])).
% 16.08/7.07  tff(c_30846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16708, c_30845])).
% 16.08/7.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.08/7.07  
% 16.08/7.07  Inference rules
% 16.08/7.07  ----------------------
% 16.08/7.07  #Ref     : 0
% 16.08/7.07  #Sup     : 6890
% 16.08/7.07  #Fact    : 10
% 16.08/7.07  #Define  : 0
% 16.08/7.07  #Split   : 102
% 16.08/7.07  #Chain   : 0
% 16.08/7.07  #Close   : 0
% 16.08/7.07  
% 16.08/7.07  Ordering : KBO
% 16.08/7.07  
% 16.08/7.07  Simplification rules
% 16.08/7.07  ----------------------
% 16.08/7.07  #Subsume      : 1001
% 16.08/7.07  #Demod        : 9046
% 16.08/7.07  #Tautology    : 2163
% 16.08/7.07  #SimpNegUnit  : 441
% 16.08/7.07  #BackRed      : 256
% 16.08/7.07  
% 16.08/7.07  #Partial instantiations: 0
% 16.08/7.07  #Strategies tried      : 1
% 16.08/7.07  
% 16.08/7.07  Timing (in seconds)
% 16.08/7.07  ----------------------
% 16.08/7.07  Preprocessing        : 0.42
% 16.08/7.07  Parsing              : 0.21
% 16.08/7.07  CNF conversion       : 0.04
% 16.08/7.07  Main loop            : 5.77
% 16.08/7.07  Inferencing          : 1.65
% 16.08/7.07  Reduction            : 2.11
% 16.08/7.07  Demodulation         : 1.57
% 16.08/7.07  BG Simplification    : 0.15
% 16.08/7.07  Subsumption          : 1.48
% 16.08/7.07  Abstraction          : 0.22
% 16.08/7.07  MUC search           : 0.00
% 16.08/7.07  Cooper               : 0.00
% 16.08/7.07  Total                : 6.33
% 16.08/7.07  Index Insertion      : 0.00
% 16.08/7.07  Index Deletion       : 0.00
% 16.08/7.07  Index Matching       : 0.00
% 16.08/7.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
