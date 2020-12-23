%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 13.99s
% Output     : CNFRefutation 14.25s
% Verified   : 
% Statistics : Number of formulae       :  276 (4836 expanded)
%              Number of leaves         :   51 (1683 expanded)
%              Depth                    :   25
%              Number of atoms          :  754 (13900 expanded)
%              Number of equality atoms :  137 (3053 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_178,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_13933,plain,(
    ! [B_1049,A_1050] : k3_xboole_0(B_1049,A_1050) = k3_xboole_0(A_1050,B_1049) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13949,plain,(
    ! [A_1050] : k3_xboole_0(k1_xboole_0,A_1050) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13933,c_10])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_100,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_144,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_62,plain,(
    ! [A_108] :
      ( l1_struct_0(A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_145,plain,(
    ! [A_155] :
      ( u1_struct_0(A_155) = k2_struct_0(A_155)
      | ~ l1_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_233,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = k2_struct_0(A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_62,c_145])).

tff(c_237,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_233])).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_238,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_90])).

tff(c_7583,plain,(
    ! [B_633,A_634] :
      ( v1_tops_1(B_633,A_634)
      | k2_pre_topc(A_634,B_633) != k2_struct_0(A_634)
      | ~ m1_subset_1(B_633,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_7586,plain,(
    ! [B_633] :
      ( v1_tops_1(B_633,'#skF_5')
      | k2_pre_topc('#skF_5',B_633) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_633,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_7583])).

tff(c_7781,plain,(
    ! [B_652] :
      ( v1_tops_1(B_652,'#skF_5')
      | k2_pre_topc('#skF_5',B_652) != k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_652,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7586])).

tff(c_7784,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_238,c_7781])).

tff(c_7795,plain,(
    k2_pre_topc('#skF_5','#skF_6') != k2_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_7784])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_7910,plain,(
    ! [A_666,B_667,C_668] :
      ( r2_hidden('#skF_2'(A_666,B_667,C_668),u1_struct_0(A_666))
      | k2_pre_topc(A_666,B_667) = C_668
      | ~ m1_subset_1(C_668,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ l1_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7918,plain,(
    ! [B_667,C_668] :
      ( r2_hidden('#skF_2'('#skF_5',B_667,C_668),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_667) = C_668
      | ~ m1_subset_1(C_668,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_7910])).

tff(c_7922,plain,(
    ! [B_667,C_668] :
      ( r2_hidden('#skF_2'('#skF_5',B_667,C_668),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_667) = C_668
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_237,c_237,c_7918])).

tff(c_8329,plain,(
    ! [B_740,A_741,C_742] :
      ( r1_xboole_0(B_740,'#skF_3'(A_741,B_740,C_742))
      | ~ r2_hidden('#skF_2'(A_741,B_740,C_742),C_742)
      | k2_pre_topc(A_741,B_740) = C_742
      | ~ m1_subset_1(C_742,k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ m1_subset_1(B_740,k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ l1_pre_topc(A_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8348,plain,(
    ! [B_667] :
      ( r1_xboole_0(B_667,'#skF_3'('#skF_5',B_667,k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_667) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_7922,c_8329])).

tff(c_8358,plain,(
    ! [B_667] :
      ( r1_xboole_0(B_667,'#skF_3'('#skF_5',B_667,k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_667) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_92,c_237,c_115,c_237,c_8348])).

tff(c_8243,plain,(
    ! [A_725,B_726,C_727] :
      ( v3_pre_topc('#skF_3'(A_725,B_726,C_727),A_725)
      | ~ r2_hidden('#skF_2'(A_725,B_726,C_727),C_727)
      | k2_pre_topc(A_725,B_726) = C_727
      | ~ m1_subset_1(C_727,k1_zfmisc_1(u1_struct_0(A_725)))
      | ~ m1_subset_1(B_726,k1_zfmisc_1(u1_struct_0(A_725)))
      | ~ l1_pre_topc(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8256,plain,(
    ! [B_667] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_667,k2_struct_0('#skF_5')),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_667) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_7922,c_8243])).

tff(c_8264,plain,(
    ! [B_667] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_667,k2_struct_0('#skF_5')),'#skF_5')
      | k2_pre_topc('#skF_5',B_667) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_92,c_237,c_115,c_237,c_8256])).

tff(c_8575,plain,(
    ! [A_768,B_769,C_770] :
      ( m1_subset_1('#skF_3'(A_768,B_769,C_770),k1_zfmisc_1(u1_struct_0(A_768)))
      | ~ r2_hidden('#skF_2'(A_768,B_769,C_770),C_770)
      | k2_pre_topc(A_768,B_769) = C_770
      | ~ m1_subset_1(C_770,k1_zfmisc_1(u1_struct_0(A_768)))
      | ~ m1_subset_1(B_769,k1_zfmisc_1(u1_struct_0(A_768)))
      | ~ l1_pre_topc(A_768) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8588,plain,(
    ! [B_667] :
      ( m1_subset_1('#skF_3'('#skF_5',B_667,k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_667) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_7922,c_8575])).

tff(c_8600,plain,(
    ! [B_771] :
      ( m1_subset_1('#skF_3'('#skF_5',B_771,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | k2_pre_topc('#skF_5',B_771) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_771,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_92,c_237,c_115,c_237,c_237,c_8588])).

tff(c_114,plain,(
    ! [C_148] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_148)
      | ~ v3_pre_topc(C_148,'#skF_5')
      | k1_xboole_0 = C_148
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_7503,plain,(
    ! [C_148] :
      ( v1_tops_1('#skF_6','#skF_5')
      | ~ r1_xboole_0('#skF_6',C_148)
      | ~ v3_pre_topc(C_148,'#skF_5')
      | k1_xboole_0 = C_148
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_114])).

tff(c_7504,plain,(
    ! [C_148] :
      ( ~ r1_xboole_0('#skF_6',C_148)
      | ~ v3_pre_topc(C_148,'#skF_5')
      | k1_xboole_0 = C_148
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_7503])).

tff(c_8844,plain,(
    ! [B_794] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_794,k2_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_3'('#skF_5',B_794,k2_struct_0('#skF_5')),'#skF_5')
      | '#skF_3'('#skF_5',B_794,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_794) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_794,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_8600,c_7504])).

tff(c_10562,plain,(
    ! [B_915] :
      ( ~ r1_xboole_0('#skF_6','#skF_3'('#skF_5',B_915,k2_struct_0('#skF_5')))
      | '#skF_3'('#skF_5',B_915,k2_struct_0('#skF_5')) = k1_xboole_0
      | k2_pre_topc('#skF_5',B_915) = k2_struct_0('#skF_5')
      | ~ m1_subset_1(B_915,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_8264,c_8844])).

tff(c_10566,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_8358,c_10562])).

tff(c_10572,plain,
    ( '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_10566])).

tff(c_10573,plain,(
    '#skF_3'('#skF_5','#skF_6',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7795,c_10572])).

tff(c_10599,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10573,c_8264])).

tff(c_10618,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_10599])).

tff(c_10619,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_7795,c_10618])).

tff(c_32,plain,(
    ! [A_23,B_67,C_89] :
      ( r2_hidden('#skF_2'(A_23,B_67,C_89),'#skF_3'(A_23,B_67,C_89))
      | ~ r2_hidden('#skF_2'(A_23,B_67,C_89),C_89)
      | k2_pre_topc(A_23,B_67) = C_89
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10590,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10573,c_32])).

tff(c_10609,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_238,c_237,c_115,c_237,c_10590])).

tff(c_10610,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0)
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_7795,c_10609])).

tff(c_10712,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10610])).

tff(c_10721,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_7922,c_10712])).

tff(c_10726,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_115,c_10721])).

tff(c_10728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7795,c_10726])).

tff(c_10729,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10610])).

tff(c_22,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_347,plain,(
    ! [A_176,C_177,B_178] :
      ( m1_subset_1(A_176,C_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(C_177))
      | ~ r2_hidden(A_176,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_356,plain,(
    ! [A_176,A_17] :
      ( m1_subset_1(A_176,A_17)
      | ~ r2_hidden(A_176,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_347])).

tff(c_10779,plain,(
    ! [A_17] : m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_17) ),
    inference(resolution,[status(thm)],[c_10729,c_356])).

tff(c_20,plain,(
    ! [C_16,A_13,B_14] :
      ( r2_hidden(C_16,A_13)
      | ~ r2_hidden(C_16,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10761,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_13)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_10729,c_20])).

tff(c_10783,plain,(
    ! [A_13] : r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10761])).

tff(c_8449,plain,(
    ! [B_752,D_753,C_754,A_755] :
      ( ~ r1_xboole_0(B_752,D_753)
      | ~ r2_hidden(C_754,D_753)
      | ~ v3_pre_topc(D_753,A_755)
      | ~ m1_subset_1(D_753,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ r2_hidden(C_754,k2_pre_topc(A_755,B_752))
      | ~ m1_subset_1(C_754,u1_struct_0(A_755))
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ l1_pre_topc(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12076,plain,(
    ! [C_976,B_977,A_978,A_979] :
      ( ~ r2_hidden(C_976,B_977)
      | ~ v3_pre_topc(B_977,A_978)
      | ~ m1_subset_1(B_977,k1_zfmisc_1(u1_struct_0(A_978)))
      | ~ r2_hidden(C_976,k2_pre_topc(A_978,A_979))
      | ~ m1_subset_1(C_976,u1_struct_0(A_978))
      | ~ m1_subset_1(A_979,k1_zfmisc_1(u1_struct_0(A_978)))
      | ~ l1_pre_topc(A_978)
      | k3_xboole_0(A_979,B_977) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_8449])).

tff(c_12084,plain,(
    ! [A_13,A_978,A_979] :
      ( ~ v3_pre_topc(A_13,A_978)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(u1_struct_0(A_978)))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),k2_pre_topc(A_978,A_979))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6',k2_struct_0('#skF_5')),u1_struct_0(A_978))
      | ~ m1_subset_1(A_979,k1_zfmisc_1(u1_struct_0(A_978)))
      | ~ l1_pre_topc(A_978)
      | k3_xboole_0(A_979,A_13) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10783,c_12076])).

tff(c_13821,plain,(
    ! [A_1039,A_1040,A_1041] :
      ( ~ v3_pre_topc(A_1039,A_1040)
      | ~ m1_subset_1(A_1039,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ m1_subset_1(A_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_pre_topc(A_1040)
      | k3_xboole_0(A_1041,A_1039) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10779,c_10783,c_12084])).

tff(c_13849,plain,(
    ! [A_1040,A_1041] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1040)
      | ~ m1_subset_1(A_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_pre_topc(A_1040)
      | k3_xboole_0(A_1041,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_13821])).

tff(c_13869,plain,(
    ! [A_1045,A_1046] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1045)
      | ~ m1_subset_1(A_1046,k1_zfmisc_1(u1_struct_0(A_1045)))
      | ~ l1_pre_topc(A_1045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13849])).

tff(c_13916,plain,(
    ! [A_1047] :
      ( ~ v3_pre_topc(k1_xboole_0,A_1047)
      | ~ l1_pre_topc(A_1047) ) ),
    inference(resolution,[status(thm)],[c_10779,c_13869])).

tff(c_13919,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10619,c_13916])).

tff(c_13923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13919])).

tff(c_13924,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_13928,plain,(
    ! [A_1048] :
      ( u1_struct_0(A_1048) = k2_struct_0(A_1048)
      | ~ l1_struct_0(A_1048) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14020,plain,(
    ! [A_1052] :
      ( u1_struct_0(A_1052) = k2_struct_0(A_1052)
      | ~ l1_pre_topc(A_1052) ) ),
    inference(resolution,[status(thm)],[c_62,c_13928])).

tff(c_14024,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_14020])).

tff(c_14194,plain,(
    ! [A_1080,B_1081] :
      ( k2_pre_topc(A_1080,B_1081) = B_1081
      | ~ v4_pre_topc(B_1081,A_1080)
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0(A_1080)))
      | ~ l1_pre_topc(A_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14197,plain,(
    ! [B_1081] :
      ( k2_pre_topc('#skF_5',B_1081) = B_1081
      | ~ v4_pre_topc(B_1081,'#skF_5')
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_14194])).

tff(c_18640,plain,(
    ! [B_1469] :
      ( k2_pre_topc('#skF_5',B_1469) = B_1469
      | ~ v4_pre_topc(B_1469,'#skF_5')
      | ~ m1_subset_1(B_1469,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14197])).

tff(c_18660,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_18640])).

tff(c_22874,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18660])).

tff(c_94,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_13925,plain,(
    v1_tops_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_14026,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14024,c_90])).

tff(c_18612,plain,(
    ! [A_1465,B_1466] :
      ( k2_pre_topc(A_1465,B_1466) = k2_struct_0(A_1465)
      | ~ v1_tops_1(B_1466,A_1465)
      | ~ m1_subset_1(B_1466,k1_zfmisc_1(u1_struct_0(A_1465)))
      | ~ l1_pre_topc(A_1465) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18615,plain,(
    ! [B_1466] :
      ( k2_pre_topc('#skF_5',B_1466) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1466,'#skF_5')
      | ~ m1_subset_1(B_1466,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_18612])).

tff(c_18879,plain,(
    ! [B_1488] :
      ( k2_pre_topc('#skF_5',B_1488) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1488,'#skF_5')
      | ~ m1_subset_1(B_1488,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_18615])).

tff(c_18882,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_14026,c_18879])).

tff(c_18896,plain,(
    k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_18882])).

tff(c_18655,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_14026,c_18640])).

tff(c_18661,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18655])).

tff(c_18786,plain,(
    ! [B_1479,A_1480] :
      ( v4_pre_topc(B_1479,A_1480)
      | k2_pre_topc(A_1480,B_1479) != B_1479
      | ~ v2_pre_topc(A_1480)
      | ~ m1_subset_1(B_1479,k1_zfmisc_1(u1_struct_0(A_1480)))
      | ~ l1_pre_topc(A_1480) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18789,plain,(
    ! [B_1479] :
      ( v4_pre_topc(B_1479,'#skF_5')
      | k2_pre_topc('#skF_5',B_1479) != B_1479
      | ~ v2_pre_topc('#skF_5')
      | ~ m1_subset_1(B_1479,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_18786])).

tff(c_18834,plain,(
    ! [B_1484] :
      ( v4_pre_topc(B_1484,'#skF_5')
      | k2_pre_topc('#skF_5',B_1484) != B_1484
      | ~ m1_subset_1(B_1484,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_18789])).

tff(c_18837,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_14026,c_18834])).

tff(c_18851,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_18661,c_18837])).

tff(c_18903,plain,(
    k2_struct_0('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18896,c_18851])).

tff(c_22768,plain,(
    ! [A_1797,B_1798,C_1799] :
      ( r2_hidden('#skF_2'(A_1797,B_1798,C_1799),u1_struct_0(A_1797))
      | k2_pre_topc(A_1797,B_1798) = C_1799
      | ~ m1_subset_1(C_1799,k1_zfmisc_1(u1_struct_0(A_1797)))
      | ~ m1_subset_1(B_1798,k1_zfmisc_1(u1_struct_0(A_1797)))
      | ~ l1_pre_topc(A_1797) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22776,plain,(
    ! [B_1798,C_1799] :
      ( r2_hidden('#skF_2'('#skF_5',B_1798,C_1799),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1798) = C_1799
      | ~ m1_subset_1(C_1799,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1798,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_22768])).

tff(c_22784,plain,(
    ! [B_1803,C_1804] :
      ( r2_hidden('#skF_2'('#skF_5',B_1803,C_1804),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1803) = C_1804
      | ~ m1_subset_1(C_1804,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1803,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14024,c_14024,c_22776])).

tff(c_14152,plain,(
    ! [A_1066,C_1067,B_1068] :
      ( m1_subset_1(A_1066,C_1067)
      | ~ m1_subset_1(B_1068,k1_zfmisc_1(C_1067))
      | ~ r2_hidden(A_1066,B_1068) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14163,plain,(
    ! [A_1066,A_12] :
      ( m1_subset_1(A_1066,A_12)
      | ~ r2_hidden(A_1066,A_12) ) ),
    inference(resolution,[status(thm)],[c_115,c_14152])).

tff(c_22795,plain,(
    ! [B_1803,C_1804] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1803,C_1804),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1803) = C_1804
      | ~ m1_subset_1(C_1804,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1803,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_22784,c_14163])).

tff(c_84,plain,(
    ! [A_137] :
      ( v3_pre_topc(k2_struct_0(A_137),A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_18679,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18660])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14176,plain,(
    ! [A_1078,B_1079] :
      ( k4_xboole_0(A_1078,B_1079) = k3_subset_1(A_1078,B_1079)
      | ~ m1_subset_1(B_1079,k1_zfmisc_1(A_1078)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14188,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = k3_subset_1(A_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_14176])).

tff(c_14193,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14188])).

tff(c_18724,plain,(
    ! [B_1475,A_1476] :
      ( v4_pre_topc(B_1475,A_1476)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1476),B_1475),A_1476)
      | ~ m1_subset_1(B_1475,k1_zfmisc_1(u1_struct_0(A_1476)))
      | ~ l1_pre_topc(A_1476) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_18728,plain,(
    ! [A_1476] :
      ( v4_pre_topc(k1_xboole_0,A_1476)
      | ~ v3_pre_topc(u1_struct_0(A_1476),A_1476)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1476)))
      | ~ l1_pre_topc(A_1476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14193,c_18724])).

tff(c_18770,plain,(
    ! [A_1478] :
      ( v4_pre_topc(k1_xboole_0,A_1478)
      | ~ v3_pre_topc(u1_struct_0(A_1478),A_1478)
      | ~ l1_pre_topc(A_1478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18728])).

tff(c_18773,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_18770])).

tff(c_18775,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_18773])).

tff(c_18776,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_18679,c_18775])).

tff(c_18779,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_18776])).

tff(c_18783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_18779])).

tff(c_18784,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18660])).

tff(c_18785,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_18660])).

tff(c_18861,plain,(
    ! [A_1485,B_1486] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_1485),B_1486),A_1485)
      | ~ v4_pre_topc(B_1486,A_1485)
      | ~ m1_subset_1(B_1486,k1_zfmisc_1(u1_struct_0(A_1485)))
      | ~ l1_pre_topc(A_1485) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_18865,plain,(
    ! [A_1485] :
      ( v3_pre_topc(u1_struct_0(A_1485),A_1485)
      | ~ v4_pre_topc(k1_xboole_0,A_1485)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1485)))
      | ~ l1_pre_topc(A_1485) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14193,c_18861])).

tff(c_18873,plain,(
    ! [A_1487] :
      ( v3_pre_topc(u1_struct_0(A_1487),A_1487)
      | ~ v4_pre_topc(k1_xboole_0,A_1487)
      | ~ l1_pre_topc(A_1487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18865])).

tff(c_18876,plain,
    ( v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_18873])).

tff(c_18878,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_18785,c_18876])).

tff(c_19011,plain,(
    ! [A_1499,B_1500,C_1501] :
      ( r2_hidden('#skF_2'(A_1499,B_1500,C_1501),u1_struct_0(A_1499))
      | k2_pre_topc(A_1499,B_1500) = C_1501
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0(A_1499)))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(u1_struct_0(A_1499)))
      | ~ l1_pre_topc(A_1499) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_19019,plain,(
    ! [B_1500,C_1501] :
      ( r2_hidden('#skF_2'('#skF_5',B_1500,C_1501),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1500) = C_1501
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_19011])).

tff(c_19023,plain,(
    ! [B_1500,C_1501] :
      ( r2_hidden('#skF_2'('#skF_5',B_1500,C_1501),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1500) = C_1501
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14024,c_14024,c_19019])).

tff(c_21259,plain,(
    ! [A_1726,B_1727,C_1728,E_1729] :
      ( v3_pre_topc('#skF_3'(A_1726,B_1727,C_1728),A_1726)
      | ~ r1_xboole_0(B_1727,E_1729)
      | ~ r2_hidden('#skF_2'(A_1726,B_1727,C_1728),E_1729)
      | ~ v3_pre_topc(E_1729,A_1726)
      | ~ m1_subset_1(E_1729,k1_zfmisc_1(u1_struct_0(A_1726)))
      | k2_pre_topc(A_1726,B_1727) = C_1728
      | ~ m1_subset_1(C_1728,k1_zfmisc_1(u1_struct_0(A_1726)))
      | ~ m1_subset_1(B_1727,k1_zfmisc_1(u1_struct_0(A_1726)))
      | ~ l1_pre_topc(A_1726) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_21311,plain,(
    ! [B_1500,C_1501] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1500,C_1501),'#skF_5')
      | ~ r1_xboole_0(B_1500,k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1500) = C_1501
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_19023,c_21259])).

tff(c_21994,plain,(
    ! [B_1767,C_1768] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1767,C_1768),'#skF_5')
      | ~ r1_xboole_0(B_1767,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1767) = C_1768
      | ~ m1_subset_1(C_1768,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1767,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14024,c_14024,c_115,c_14024,c_18878,c_21311])).

tff(c_22026,plain,(
    ! [B_1769] :
      ( v3_pre_topc('#skF_3'('#skF_5',B_1769,'#skF_6'),'#skF_5')
      | ~ r1_xboole_0(B_1769,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1769) = '#skF_6'
      | ~ m1_subset_1(B_1769,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_14026,c_21994])).

tff(c_22058,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_6'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22,c_22026])).

tff(c_22072,plain,
    ( v3_pre_topc('#skF_3'('#skF_5',k1_xboole_0,'#skF_6'),'#skF_5')
    | ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18784,c_22058])).

tff(c_22158,plain,(
    ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_22072])).

tff(c_22162,plain,(
    k3_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_22158])).

tff(c_22166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13949,c_22162])).

tff(c_22168,plain,(
    r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_22072])).

tff(c_102,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_14019,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_102])).

tff(c_14025,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14024,c_14019])).

tff(c_14162,plain,(
    ! [A_1066] :
      ( m1_subset_1(A_1066,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_1066,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14025,c_14152])).

tff(c_18997,plain,(
    ! [A_1496,C_1497,B_1498] :
      ( ~ v2_struct_0(A_1496)
      | ~ r2_hidden(C_1497,k2_pre_topc(A_1496,B_1498))
      | ~ m1_subset_1(C_1497,u1_struct_0(A_1496))
      | ~ m1_subset_1(B_1498,k1_zfmisc_1(u1_struct_0(A_1496)))
      | ~ l1_pre_topc(A_1496) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19001,plain,(
    ! [C_1497] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1497,k1_xboole_0)
      | ~ m1_subset_1(C_1497,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18784,c_18997])).

tff(c_19007,plain,(
    ! [C_1497] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1497,k1_xboole_0)
      | ~ m1_subset_1(C_1497,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_22,c_14024,c_14024,c_19001])).

tff(c_19010,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_19007])).

tff(c_74,plain,(
    ! [A_112,B_124,C_130] :
      ( m1_subset_1('#skF_4'(A_112,B_124,C_130),k1_zfmisc_1(u1_struct_0(A_112)))
      | r2_hidden(C_130,k2_pre_topc(A_112,B_124))
      | v2_struct_0(A_112)
      | ~ m1_subset_1(C_130,u1_struct_0(A_112))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19053,plain,(
    ! [C_1512,A_1513,B_1514] :
      ( r2_hidden(C_1512,'#skF_4'(A_1513,B_1514,C_1512))
      | r2_hidden(C_1512,k2_pre_topc(A_1513,B_1514))
      | v2_struct_0(A_1513)
      | ~ m1_subset_1(C_1512,u1_struct_0(A_1513))
      | ~ m1_subset_1(B_1514,k1_zfmisc_1(u1_struct_0(A_1513)))
      | ~ l1_pre_topc(A_1513) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19055,plain,(
    ! [C_1512,B_1514] :
      ( r2_hidden(C_1512,'#skF_4'('#skF_5',B_1514,C_1512))
      | r2_hidden(C_1512,k2_pre_topc('#skF_5',B_1514))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1512,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1514,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_19053])).

tff(c_19063,plain,(
    ! [C_1512,B_1514] :
      ( r2_hidden(C_1512,'#skF_4'('#skF_5',B_1514,C_1512))
      | r2_hidden(C_1512,k2_pre_topc('#skF_5',B_1514))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_1512,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1514,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14024,c_19055])).

tff(c_19102,plain,(
    ! [C_1520,B_1521] :
      ( r2_hidden(C_1520,'#skF_4'('#skF_5',B_1521,C_1520))
      | r2_hidden(C_1520,k2_pre_topc('#skF_5',B_1521))
      | ~ m1_subset_1(C_1520,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19010,c_19063])).

tff(c_19104,plain,(
    ! [C_1520] :
      ( r2_hidden(C_1520,'#skF_4'('#skF_5','#skF_6',C_1520))
      | r2_hidden(C_1520,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1520,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14026,c_19102])).

tff(c_19132,plain,(
    ! [C_1525] :
      ( r2_hidden(C_1525,'#skF_4'('#skF_5','#skF_6',C_1525))
      | r2_hidden(C_1525,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1525,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18896,c_19104])).

tff(c_19291,plain,(
    ! [C_1546,A_1547] :
      ( r2_hidden(C_1546,A_1547)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1546),k1_zfmisc_1(A_1547))
      | r2_hidden(C_1546,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1546,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_19132,c_20])).

tff(c_19295,plain,(
    ! [C_130] :
      ( r2_hidden(C_130,u1_struct_0('#skF_5'))
      | r2_hidden(C_130,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_130,k2_struct_0('#skF_5'))
      | r2_hidden(C_130,k2_pre_topc('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_19291])).

tff(c_19302,plain,(
    ! [C_130] :
      ( r2_hidden(C_130,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_130,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14026,c_14024,c_14024,c_18896,c_14024,c_19295])).

tff(c_19303,plain,(
    ! [C_130] :
      ( r2_hidden(C_130,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_130,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19010,c_19302])).

tff(c_98,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_13927,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_98])).

tff(c_96,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_14014,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_96])).

tff(c_19527,plain,(
    ! [B_1582,D_1583,C_1584,A_1585] :
      ( ~ r1_xboole_0(B_1582,D_1583)
      | ~ r2_hidden(C_1584,D_1583)
      | ~ v3_pre_topc(D_1583,A_1585)
      | ~ m1_subset_1(D_1583,k1_zfmisc_1(u1_struct_0(A_1585)))
      | ~ r2_hidden(C_1584,k2_pre_topc(A_1585,B_1582))
      | ~ m1_subset_1(C_1584,u1_struct_0(A_1585))
      | ~ m1_subset_1(B_1582,k1_zfmisc_1(u1_struct_0(A_1585)))
      | ~ l1_pre_topc(A_1585) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19569,plain,(
    ! [C_1590,A_1591] :
      ( ~ r2_hidden(C_1590,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_1591)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_1591)))
      | ~ r2_hidden(C_1590,k2_pre_topc(A_1591,'#skF_6'))
      | ~ m1_subset_1(C_1590,u1_struct_0(A_1591))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1591)))
      | ~ l1_pre_topc(A_1591) ) ),
    inference(resolution,[status(thm)],[c_14014,c_19527])).

tff(c_19571,plain,(
    ! [C_1590] :
      ( ~ r2_hidden(C_1590,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(C_1590,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_1590,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14024,c_19569])).

tff(c_19574,plain,(
    ! [C_1592] :
      ( ~ r2_hidden(C_1592,'#skF_7')
      | ~ r2_hidden(C_1592,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1592,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14026,c_14024,c_14024,c_18896,c_14025,c_13927,c_19571])).

tff(c_19583,plain,(
    ! [C_1593] :
      ( ~ r2_hidden(C_1593,'#skF_7')
      | ~ m1_subset_1(C_1593,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_19303,c_19574])).

tff(c_19594,plain,(
    ! [A_1066] : ~ r2_hidden(A_1066,'#skF_7') ),
    inference(resolution,[status(thm)],[c_14162,c_19583])).

tff(c_21458,plain,(
    ! [A_1744,B_1745,C_1746,E_1747] :
      ( r2_hidden('#skF_2'(A_1744,B_1745,C_1746),C_1746)
      | ~ r1_xboole_0(B_1745,E_1747)
      | ~ r2_hidden('#skF_2'(A_1744,B_1745,C_1746),E_1747)
      | ~ v3_pre_topc(E_1747,A_1744)
      | ~ m1_subset_1(E_1747,k1_zfmisc_1(u1_struct_0(A_1744)))
      | k2_pre_topc(A_1744,B_1745) = C_1746
      | ~ m1_subset_1(C_1746,k1_zfmisc_1(u1_struct_0(A_1744)))
      | ~ m1_subset_1(B_1745,k1_zfmisc_1(u1_struct_0(A_1744)))
      | ~ l1_pre_topc(A_1744) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_21510,plain,(
    ! [B_1500,C_1501] :
      ( r2_hidden('#skF_2'('#skF_5',B_1500,C_1501),C_1501)
      | ~ r1_xboole_0(B_1500,k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1500) = C_1501
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1500,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_19023,c_21458])).

tff(c_22668,plain,(
    ! [B_1793,C_1794] :
      ( r2_hidden('#skF_2'('#skF_5',B_1793,C_1794),C_1794)
      | ~ r1_xboole_0(B_1793,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1793) = C_1794
      | ~ m1_subset_1(C_1794,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1793,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14024,c_14024,c_115,c_14024,c_18878,c_21510])).

tff(c_22684,plain,(
    ! [B_1793] :
      ( r2_hidden('#skF_2'('#skF_5',B_1793,'#skF_7'),'#skF_7')
      | ~ r1_xboole_0(B_1793,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1793) = '#skF_7'
      | ~ m1_subset_1(B_1793,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_14025,c_22668])).

tff(c_22702,plain,(
    ! [B_1795] :
      ( ~ r1_xboole_0(B_1795,k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1795) = '#skF_7'
      | ~ m1_subset_1(B_1795,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19594,c_22684])).

tff(c_22734,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k2_struct_0('#skF_5'))
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22,c_22702])).

tff(c_22748,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18784,c_22168,c_22734])).

tff(c_22750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13924,c_22748])).

tff(c_22752,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_19007])).

tff(c_18999,plain,(
    ! [C_1497] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1497,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1497,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18896,c_18997])).

tff(c_19005,plain,(
    ! [C_1497] :
      ( ~ v2_struct_0('#skF_5')
      | ~ r2_hidden(C_1497,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1497,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14026,c_14024,c_14024,c_18999])).

tff(c_22753,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_19005])).

tff(c_22755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22752,c_22753])).

tff(c_22756,plain,(
    ! [C_1497] :
      ( ~ r2_hidden(C_1497,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1497,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_19005])).

tff(c_22804,plain,(
    ! [B_1809,C_1810] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',B_1809,C_1810),k2_struct_0('#skF_5'))
      | k2_pre_topc('#skF_5',B_1809) = C_1810
      | ~ m1_subset_1(C_1810,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1809,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_22784,c_22756])).

tff(c_22817,plain,(
    ! [B_1811,C_1812] :
      ( k2_pre_topc('#skF_5',B_1811) = C_1812
      | ~ m1_subset_1(C_1812,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1811,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_22795,c_22804])).

tff(c_22845,plain,(
    ! [B_1816] :
      ( k2_pre_topc('#skF_5',B_1816) = '#skF_6'
      | ~ m1_subset_1(B_1816,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_14026,c_22817])).

tff(c_22860,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14026,c_22845])).

tff(c_22864,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22860,c_18896])).

tff(c_22866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18903,c_22864])).

tff(c_22867,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18655])).

tff(c_22931,plain,(
    ! [B_1822] :
      ( k2_pre_topc('#skF_5',B_1822) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1822,'#skF_5')
      | ~ m1_subset_1(B_1822,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_18615])).

tff(c_22934,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_14026,c_22931])).

tff(c_22948,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_22867,c_22934])).

tff(c_22998,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22948,c_84])).

tff(c_23002,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_22998])).

tff(c_22988,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22948,c_14024])).

tff(c_23061,plain,(
    ! [B_1825,A_1826] :
      ( v4_pre_topc(B_1825,A_1826)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1826),B_1825),A_1826)
      | ~ m1_subset_1(B_1825,k1_zfmisc_1(u1_struct_0(A_1826)))
      | ~ l1_pre_topc(A_1826) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_23068,plain,(
    ! [A_1826] :
      ( v4_pre_topc(k1_xboole_0,A_1826)
      | ~ v3_pre_topc(u1_struct_0(A_1826),A_1826)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1826)))
      | ~ l1_pre_topc(A_1826) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14193,c_23061])).

tff(c_23097,plain,(
    ! [A_1829] :
      ( v4_pre_topc(k1_xboole_0,A_1829)
      | ~ v3_pre_topc(u1_struct_0(A_1829),A_1829)
      | ~ l1_pre_topc(A_1829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_23068])).

tff(c_23100,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22988,c_23097])).

tff(c_23102,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23002,c_23100])).

tff(c_23104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22874,c_23102])).

tff(c_23105,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18660])).

tff(c_23538,plain,(
    ! [B_1861] :
      ( k2_pre_topc('#skF_5',B_1861) = k2_struct_0('#skF_5')
      | ~ v1_tops_1(B_1861,'#skF_5')
      | ~ m1_subset_1(B_1861,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_18615])).

tff(c_23541,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = k2_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_14026,c_23538])).

tff(c_23555,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13925,c_22867,c_23541])).

tff(c_23579,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23555,c_14025])).

tff(c_23580,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23555,c_14024])).

tff(c_23802,plain,(
    ! [A_1874,B_1875,C_1876] :
      ( r2_hidden('#skF_2'(A_1874,B_1875,C_1876),u1_struct_0(A_1874))
      | k2_pre_topc(A_1874,B_1875) = C_1876
      | ~ m1_subset_1(C_1876,k1_zfmisc_1(u1_struct_0(A_1874)))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1(u1_struct_0(A_1874)))
      | ~ l1_pre_topc(A_1874) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_23810,plain,(
    ! [B_1875,C_1876] :
      ( r2_hidden('#skF_2'('#skF_5',B_1875,C_1876),'#skF_6')
      | k2_pre_topc('#skF_5',B_1875) = C_1876
      | ~ m1_subset_1(C_1876,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23580,c_23802])).

tff(c_23831,plain,(
    ! [B_1878,C_1879] :
      ( r2_hidden('#skF_2'('#skF_5',B_1878,C_1879),'#skF_6')
      | k2_pre_topc('#skF_5',B_1878) = C_1879
      | ~ m1_subset_1(C_1879,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_1878,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23580,c_23580,c_23810])).

tff(c_23837,plain,(
    ! [B_1878,C_1879,A_13] :
      ( r2_hidden('#skF_2'('#skF_5',B_1878,C_1879),A_13)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_13))
      | k2_pre_topc('#skF_5',B_1878) = C_1879
      | ~ m1_subset_1(C_1879,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_1878,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23831,c_20])).

tff(c_23590,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23555,c_84])).

tff(c_23594,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_23590])).

tff(c_23814,plain,(
    ! [B_1875,C_1876] :
      ( r2_hidden('#skF_2'('#skF_5',B_1875,C_1876),'#skF_6')
      | k2_pre_topc('#skF_5',B_1875) = C_1876
      | ~ m1_subset_1(C_1876,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23580,c_23580,c_23810])).

tff(c_26408,plain,(
    ! [A_2111,B_2112,C_2113,E_2114] :
      ( r2_hidden('#skF_2'(A_2111,B_2112,C_2113),C_2113)
      | ~ r1_xboole_0(B_2112,E_2114)
      | ~ r2_hidden('#skF_2'(A_2111,B_2112,C_2113),E_2114)
      | ~ v3_pre_topc(E_2114,A_2111)
      | ~ m1_subset_1(E_2114,k1_zfmisc_1(u1_struct_0(A_2111)))
      | k2_pre_topc(A_2111,B_2112) = C_2113
      | ~ m1_subset_1(C_2113,k1_zfmisc_1(u1_struct_0(A_2111)))
      | ~ m1_subset_1(B_2112,k1_zfmisc_1(u1_struct_0(A_2111)))
      | ~ l1_pre_topc(A_2111) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26471,plain,(
    ! [B_1875,C_1876] :
      ( r2_hidden('#skF_2'('#skF_5',B_1875,C_1876),C_1876)
      | ~ r1_xboole_0(B_1875,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_1876,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | k2_pre_topc('#skF_5',B_1875) = C_1876
      | ~ m1_subset_1(C_1876,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23814,c_26408])).

tff(c_26582,plain,(
    ! [B_2123,C_2124] :
      ( r2_hidden('#skF_2'('#skF_5',B_2123,C_2124),C_2124)
      | ~ r1_xboole_0(B_2123,'#skF_6')
      | k2_pre_topc('#skF_5',B_2123) = C_2124
      | ~ m1_subset_1(C_2124,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_2123,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23580,c_23580,c_115,c_23580,c_23594,c_26471])).

tff(c_25751,plain,(
    ! [B_2079,E_2080,D_2081,A_2082] :
      ( ~ r1_xboole_0(B_2079,E_2080)
      | ~ r2_hidden(D_2081,E_2080)
      | ~ v3_pre_topc(E_2080,A_2082)
      | ~ m1_subset_1(E_2080,k1_zfmisc_1(u1_struct_0(A_2082)))
      | ~ r2_hidden(D_2081,k2_pre_topc(A_2082,B_2079))
      | ~ r2_hidden(D_2081,u1_struct_0(A_2082))
      | ~ m1_subset_1(k2_pre_topc(A_2082,B_2079),k1_zfmisc_1(u1_struct_0(A_2082)))
      | ~ m1_subset_1(B_2079,k1_zfmisc_1(u1_struct_0(A_2082)))
      | ~ l1_pre_topc(A_2082) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_25808,plain,(
    ! [D_2086,A_2087] :
      ( ~ r2_hidden(D_2086,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_2087)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_2087)))
      | ~ r2_hidden(D_2086,k2_pre_topc(A_2087,'#skF_6'))
      | ~ r2_hidden(D_2086,u1_struct_0(A_2087))
      | ~ m1_subset_1(k2_pre_topc(A_2087,'#skF_6'),k1_zfmisc_1(u1_struct_0(A_2087)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2087)))
      | ~ l1_pre_topc(A_2087) ) ),
    inference(resolution,[status(thm)],[c_14014,c_25751])).

tff(c_25828,plain,(
    ! [D_2086] :
      ( ~ r2_hidden(D_2086,'#skF_7')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(D_2086,'#skF_6')
      | ~ r2_hidden(D_2086,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22867,c_25808])).

tff(c_25846,plain,(
    ! [D_2086] :
      ( ~ r2_hidden(D_2086,'#skF_7')
      | ~ r2_hidden(D_2086,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_115,c_23580,c_115,c_23580,c_22867,c_23580,c_23579,c_23580,c_13927,c_25828])).

tff(c_26595,plain,(
    ! [B_2123] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_2123,'#skF_7'),'#skF_6')
      | ~ r1_xboole_0(B_2123,'#skF_6')
      | k2_pre_topc('#skF_5',B_2123) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_2123,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26582,c_25846])).

tff(c_26669,plain,(
    ! [B_2125] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_2125,'#skF_7'),'#skF_6')
      | ~ r1_xboole_0(B_2125,'#skF_6')
      | k2_pre_topc('#skF_5',B_2125) = '#skF_7'
      | ~ m1_subset_1(B_2125,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23579,c_26595])).

tff(c_26677,plain,(
    ! [B_1878] :
      ( ~ r1_xboole_0(B_1878,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
      | k2_pre_topc('#skF_5',B_1878) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_1878,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23837,c_26669])).

tff(c_26689,plain,(
    ! [B_2126] :
      ( ~ r1_xboole_0(B_2126,'#skF_6')
      | k2_pre_topc('#skF_5',B_2126) = '#skF_7'
      | ~ m1_subset_1(B_2126,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23579,c_115,c_26677])).

tff(c_26717,plain,
    ( ~ r1_xboole_0(k1_xboole_0,'#skF_6')
    | k2_pre_topc('#skF_5',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22,c_26689])).

tff(c_26729,plain,
    ( ~ r1_xboole_0(k1_xboole_0,'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23105,c_26717])).

tff(c_26730,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_13924,c_26729])).

tff(c_26733,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_26730])).

tff(c_26737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13949,c_26733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.99/6.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.14/6.20  
% 14.14/6.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.14/6.20  %$ v4_pre_topc > v3_pre_topc > v1_tops_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 14.14/6.20  
% 14.14/6.20  %Foreground sorts:
% 14.14/6.20  
% 14.14/6.20  
% 14.14/6.20  %Background operators:
% 14.14/6.20  
% 14.14/6.20  
% 14.14/6.20  %Foreground operators:
% 14.14/6.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.14/6.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.14/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.14/6.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.14/6.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.14/6.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.14/6.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.14/6.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.14/6.20  tff('#skF_7', type, '#skF_7': $i).
% 14.14/6.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.14/6.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.14/6.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.14/6.20  tff('#skF_5', type, '#skF_5': $i).
% 14.14/6.20  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 14.14/6.20  tff('#skF_6', type, '#skF_6': $i).
% 14.14/6.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.14/6.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.14/6.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.14/6.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.14/6.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.14/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.14/6.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.14/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.14/6.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.14/6.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.14/6.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 14.14/6.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.14/6.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.14/6.20  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.14/6.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.14/6.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.14/6.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.14/6.20  
% 14.25/6.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.25/6.23  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 14.25/6.23  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.25/6.23  tff(f_178, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(C = k1_xboole_0) & v3_pre_topc(C, A)) & r1_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 14.25/6.23  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.25/6.23  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 14.25/6.23  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 14.25/6.23  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.25/6.23  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.25/6.23  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k2_pre_topc(A, B)) <=> (![D]: (r2_hidden(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(E, A) & r2_hidden(D, E)) & r1_xboole_0(B, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 14.25/6.23  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.25/6.23  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 14.25/6.23  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 14.25/6.23  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 14.25/6.23  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.25/6.23  tff(f_148, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 14.25/6.23  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.25/6.23  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.25/6.23  tff(f_157, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 14.25/6.23  tff(c_13933, plain, (![B_1049, A_1050]: (k3_xboole_0(B_1049, A_1050)=k3_xboole_0(A_1050, B_1049))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.25/6.23  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.25/6.23  tff(c_13949, plain, (![A_1050]: (k3_xboole_0(k1_xboole_0, A_1050)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13933, c_10])).
% 14.25/6.23  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.25/6.23  tff(c_92, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_100, plain, (k1_xboole_0!='#skF_7' | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_144, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 14.25/6.23  tff(c_62, plain, (![A_108]: (l1_struct_0(A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.25/6.23  tff(c_145, plain, (![A_155]: (u1_struct_0(A_155)=k2_struct_0(A_155) | ~l1_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.25/6.23  tff(c_233, plain, (![A_159]: (u1_struct_0(A_159)=k2_struct_0(A_159) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_62, c_145])).
% 14.25/6.23  tff(c_237, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_92, c_233])).
% 14.25/6.23  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_238, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_90])).
% 14.25/6.23  tff(c_7583, plain, (![B_633, A_634]: (v1_tops_1(B_633, A_634) | k2_pre_topc(A_634, B_633)!=k2_struct_0(A_634) | ~m1_subset_1(B_633, k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634))), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.25/6.23  tff(c_7586, plain, (![B_633]: (v1_tops_1(B_633, '#skF_5') | k2_pre_topc('#skF_5', B_633)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_633, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_7583])).
% 14.25/6.23  tff(c_7781, plain, (![B_652]: (v1_tops_1(B_652, '#skF_5') | k2_pre_topc('#skF_5', B_652)!=k2_struct_0('#skF_5') | ~m1_subset_1(B_652, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_7586])).
% 14.25/6.23  tff(c_7784, plain, (v1_tops_1('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_238, c_7781])).
% 14.25/6.23  tff(c_7795, plain, (k2_pre_topc('#skF_5', '#skF_6')!=k2_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_144, c_7784])).
% 14.25/6.23  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.25/6.23  tff(c_18, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.25/6.23  tff(c_115, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 14.25/6.23  tff(c_7910, plain, (![A_666, B_667, C_668]: (r2_hidden('#skF_2'(A_666, B_667, C_668), u1_struct_0(A_666)) | k2_pre_topc(A_666, B_667)=C_668 | ~m1_subset_1(C_668, k1_zfmisc_1(u1_struct_0(A_666))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_666))) | ~l1_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_7918, plain, (![B_667, C_668]: (r2_hidden('#skF_2'('#skF_5', B_667, C_668), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_667)=C_668 | ~m1_subset_1(C_668, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_7910])).
% 14.25/6.23  tff(c_7922, plain, (![B_667, C_668]: (r2_hidden('#skF_2'('#skF_5', B_667, C_668), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_667)=C_668 | ~m1_subset_1(C_668, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_237, c_237, c_7918])).
% 14.25/6.23  tff(c_8329, plain, (![B_740, A_741, C_742]: (r1_xboole_0(B_740, '#skF_3'(A_741, B_740, C_742)) | ~r2_hidden('#skF_2'(A_741, B_740, C_742), C_742) | k2_pre_topc(A_741, B_740)=C_742 | ~m1_subset_1(C_742, k1_zfmisc_1(u1_struct_0(A_741))) | ~m1_subset_1(B_740, k1_zfmisc_1(u1_struct_0(A_741))) | ~l1_pre_topc(A_741))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_8348, plain, (![B_667]: (r1_xboole_0(B_667, '#skF_3'('#skF_5', B_667, k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_667)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_7922, c_8329])).
% 14.25/6.23  tff(c_8358, plain, (![B_667]: (r1_xboole_0(B_667, '#skF_3'('#skF_5', B_667, k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_667)=k2_struct_0('#skF_5') | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_92, c_237, c_115, c_237, c_8348])).
% 14.25/6.23  tff(c_8243, plain, (![A_725, B_726, C_727]: (v3_pre_topc('#skF_3'(A_725, B_726, C_727), A_725) | ~r2_hidden('#skF_2'(A_725, B_726, C_727), C_727) | k2_pre_topc(A_725, B_726)=C_727 | ~m1_subset_1(C_727, k1_zfmisc_1(u1_struct_0(A_725))) | ~m1_subset_1(B_726, k1_zfmisc_1(u1_struct_0(A_725))) | ~l1_pre_topc(A_725))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_8256, plain, (![B_667]: (v3_pre_topc('#skF_3'('#skF_5', B_667, k2_struct_0('#skF_5')), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_667)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_7922, c_8243])).
% 14.25/6.23  tff(c_8264, plain, (![B_667]: (v3_pre_topc('#skF_3'('#skF_5', B_667, k2_struct_0('#skF_5')), '#skF_5') | k2_pre_topc('#skF_5', B_667)=k2_struct_0('#skF_5') | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_92, c_237, c_115, c_237, c_8256])).
% 14.25/6.23  tff(c_8575, plain, (![A_768, B_769, C_770]: (m1_subset_1('#skF_3'(A_768, B_769, C_770), k1_zfmisc_1(u1_struct_0(A_768))) | ~r2_hidden('#skF_2'(A_768, B_769, C_770), C_770) | k2_pre_topc(A_768, B_769)=C_770 | ~m1_subset_1(C_770, k1_zfmisc_1(u1_struct_0(A_768))) | ~m1_subset_1(B_769, k1_zfmisc_1(u1_struct_0(A_768))) | ~l1_pre_topc(A_768))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_8588, plain, (![B_667]: (m1_subset_1('#skF_3'('#skF_5', B_667, k2_struct_0('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_667)=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_667, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_7922, c_8575])).
% 14.25/6.23  tff(c_8600, plain, (![B_771]: (m1_subset_1('#skF_3'('#skF_5', B_771, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | k2_pre_topc('#skF_5', B_771)=k2_struct_0('#skF_5') | ~m1_subset_1(B_771, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_92, c_237, c_115, c_237, c_237, c_8588])).
% 14.25/6.23  tff(c_114, plain, (![C_148]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_148) | ~v3_pre_topc(C_148, '#skF_5') | k1_xboole_0=C_148 | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_7503, plain, (![C_148]: (v1_tops_1('#skF_6', '#skF_5') | ~r1_xboole_0('#skF_6', C_148) | ~v3_pre_topc(C_148, '#skF_5') | k1_xboole_0=C_148 | ~m1_subset_1(C_148, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_114])).
% 14.25/6.23  tff(c_7504, plain, (![C_148]: (~r1_xboole_0('#skF_6', C_148) | ~v3_pre_topc(C_148, '#skF_5') | k1_xboole_0=C_148 | ~m1_subset_1(C_148, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_144, c_7503])).
% 14.25/6.23  tff(c_8844, plain, (![B_794]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_794, k2_struct_0('#skF_5'))) | ~v3_pre_topc('#skF_3'('#skF_5', B_794, k2_struct_0('#skF_5')), '#skF_5') | '#skF_3'('#skF_5', B_794, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_794)=k2_struct_0('#skF_5') | ~m1_subset_1(B_794, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_8600, c_7504])).
% 14.25/6.23  tff(c_10562, plain, (![B_915]: (~r1_xboole_0('#skF_6', '#skF_3'('#skF_5', B_915, k2_struct_0('#skF_5'))) | '#skF_3'('#skF_5', B_915, k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', B_915)=k2_struct_0('#skF_5') | ~m1_subset_1(B_915, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_8264, c_8844])).
% 14.25/6.23  tff(c_10566, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8358, c_10562])).
% 14.25/6.23  tff(c_10572, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0 | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_10566])).
% 14.25/6.23  tff(c_10573, plain, ('#skF_3'('#skF_5', '#skF_6', k2_struct_0('#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_7795, c_10572])).
% 14.25/6.23  tff(c_10599, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10573, c_8264])).
% 14.25/6.23  tff(c_10618, plain, (v3_pre_topc(k1_xboole_0, '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_10599])).
% 14.25/6.23  tff(c_10619, plain, (v3_pre_topc(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_7795, c_10618])).
% 14.25/6.23  tff(c_32, plain, (![A_23, B_67, C_89]: (r2_hidden('#skF_2'(A_23, B_67, C_89), '#skF_3'(A_23, B_67, C_89)) | ~r2_hidden('#skF_2'(A_23, B_67, C_89), C_89) | k2_pre_topc(A_23, B_67)=C_89 | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_10590, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10573, c_32])).
% 14.25/6.23  tff(c_10609, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_238, c_237, c_115, c_237, c_10590])).
% 14.25/6.23  tff(c_10610, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_7795, c_10609])).
% 14.25/6.23  tff(c_10712, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_10610])).
% 14.25/6.23  tff(c_10721, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_7922, c_10712])).
% 14.25/6.23  tff(c_10726, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_115, c_10721])).
% 14.25/6.23  tff(c_10728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7795, c_10726])).
% 14.25/6.23  tff(c_10729, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_10610])).
% 14.25/6.23  tff(c_22, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.25/6.23  tff(c_347, plain, (![A_176, C_177, B_178]: (m1_subset_1(A_176, C_177) | ~m1_subset_1(B_178, k1_zfmisc_1(C_177)) | ~r2_hidden(A_176, B_178))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.25/6.23  tff(c_356, plain, (![A_176, A_17]: (m1_subset_1(A_176, A_17) | ~r2_hidden(A_176, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_347])).
% 14.25/6.23  tff(c_10779, plain, (![A_17]: (m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_17))), inference(resolution, [status(thm)], [c_10729, c_356])).
% 14.25/6.23  tff(c_20, plain, (![C_16, A_13, B_14]: (r2_hidden(C_16, A_13) | ~r2_hidden(C_16, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.25/6.23  tff(c_10761, plain, (![A_13]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_13) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_10729, c_20])).
% 14.25/6.23  tff(c_10783, plain, (![A_13]: (r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10761])).
% 14.25/6.23  tff(c_8449, plain, (![B_752, D_753, C_754, A_755]: (~r1_xboole_0(B_752, D_753) | ~r2_hidden(C_754, D_753) | ~v3_pre_topc(D_753, A_755) | ~m1_subset_1(D_753, k1_zfmisc_1(u1_struct_0(A_755))) | ~r2_hidden(C_754, k2_pre_topc(A_755, B_752)) | ~m1_subset_1(C_754, u1_struct_0(A_755)) | ~m1_subset_1(B_752, k1_zfmisc_1(u1_struct_0(A_755))) | ~l1_pre_topc(A_755))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.25/6.23  tff(c_12076, plain, (![C_976, B_977, A_978, A_979]: (~r2_hidden(C_976, B_977) | ~v3_pre_topc(B_977, A_978) | ~m1_subset_1(B_977, k1_zfmisc_1(u1_struct_0(A_978))) | ~r2_hidden(C_976, k2_pre_topc(A_978, A_979)) | ~m1_subset_1(C_976, u1_struct_0(A_978)) | ~m1_subset_1(A_979, k1_zfmisc_1(u1_struct_0(A_978))) | ~l1_pre_topc(A_978) | k3_xboole_0(A_979, B_977)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_8449])).
% 14.25/6.23  tff(c_12084, plain, (![A_13, A_978, A_979]: (~v3_pre_topc(A_13, A_978) | ~m1_subset_1(A_13, k1_zfmisc_1(u1_struct_0(A_978))) | ~r2_hidden('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), k2_pre_topc(A_978, A_979)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_6', k2_struct_0('#skF_5')), u1_struct_0(A_978)) | ~m1_subset_1(A_979, k1_zfmisc_1(u1_struct_0(A_978))) | ~l1_pre_topc(A_978) | k3_xboole_0(A_979, A_13)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10783, c_12076])).
% 14.25/6.23  tff(c_13821, plain, (![A_1039, A_1040, A_1041]: (~v3_pre_topc(A_1039, A_1040) | ~m1_subset_1(A_1039, k1_zfmisc_1(u1_struct_0(A_1040))) | ~m1_subset_1(A_1041, k1_zfmisc_1(u1_struct_0(A_1040))) | ~l1_pre_topc(A_1040) | k3_xboole_0(A_1041, A_1039)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10779, c_10783, c_12084])).
% 14.25/6.23  tff(c_13849, plain, (![A_1040, A_1041]: (~v3_pre_topc(k1_xboole_0, A_1040) | ~m1_subset_1(A_1041, k1_zfmisc_1(u1_struct_0(A_1040))) | ~l1_pre_topc(A_1040) | k3_xboole_0(A_1041, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_13821])).
% 14.25/6.23  tff(c_13869, plain, (![A_1045, A_1046]: (~v3_pre_topc(k1_xboole_0, A_1045) | ~m1_subset_1(A_1046, k1_zfmisc_1(u1_struct_0(A_1045))) | ~l1_pre_topc(A_1045))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13849])).
% 14.25/6.23  tff(c_13916, plain, (![A_1047]: (~v3_pre_topc(k1_xboole_0, A_1047) | ~l1_pre_topc(A_1047))), inference(resolution, [status(thm)], [c_10779, c_13869])).
% 14.25/6.23  tff(c_13919, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10619, c_13916])).
% 14.25/6.23  tff(c_13923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_13919])).
% 14.25/6.23  tff(c_13924, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_100])).
% 14.25/6.23  tff(c_13928, plain, (![A_1048]: (u1_struct_0(A_1048)=k2_struct_0(A_1048) | ~l1_struct_0(A_1048))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.25/6.23  tff(c_14020, plain, (![A_1052]: (u1_struct_0(A_1052)=k2_struct_0(A_1052) | ~l1_pre_topc(A_1052))), inference(resolution, [status(thm)], [c_62, c_13928])).
% 14.25/6.23  tff(c_14024, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_92, c_14020])).
% 14.25/6.23  tff(c_14194, plain, (![A_1080, B_1081]: (k2_pre_topc(A_1080, B_1081)=B_1081 | ~v4_pre_topc(B_1081, A_1080) | ~m1_subset_1(B_1081, k1_zfmisc_1(u1_struct_0(A_1080))) | ~l1_pre_topc(A_1080))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.25/6.23  tff(c_14197, plain, (![B_1081]: (k2_pre_topc('#skF_5', B_1081)=B_1081 | ~v4_pre_topc(B_1081, '#skF_5') | ~m1_subset_1(B_1081, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_14194])).
% 14.25/6.23  tff(c_18640, plain, (![B_1469]: (k2_pre_topc('#skF_5', B_1469)=B_1469 | ~v4_pre_topc(B_1469, '#skF_5') | ~m1_subset_1(B_1469, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14197])).
% 14.25/6.23  tff(c_18660, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_22, c_18640])).
% 14.25/6.23  tff(c_22874, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_18660])).
% 14.25/6.23  tff(c_94, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_13925, plain, (v1_tops_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 14.25/6.23  tff(c_14026, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14024, c_90])).
% 14.25/6.23  tff(c_18612, plain, (![A_1465, B_1466]: (k2_pre_topc(A_1465, B_1466)=k2_struct_0(A_1465) | ~v1_tops_1(B_1466, A_1465) | ~m1_subset_1(B_1466, k1_zfmisc_1(u1_struct_0(A_1465))) | ~l1_pre_topc(A_1465))), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.25/6.23  tff(c_18615, plain, (![B_1466]: (k2_pre_topc('#skF_5', B_1466)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1466, '#skF_5') | ~m1_subset_1(B_1466, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_18612])).
% 14.25/6.23  tff(c_18879, plain, (![B_1488]: (k2_pre_topc('#skF_5', B_1488)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1488, '#skF_5') | ~m1_subset_1(B_1488, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_18615])).
% 14.25/6.23  tff(c_18882, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_14026, c_18879])).
% 14.25/6.23  tff(c_18896, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_18882])).
% 14.25/6.23  tff(c_18655, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_14026, c_18640])).
% 14.25/6.23  tff(c_18661, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_18655])).
% 14.25/6.23  tff(c_18786, plain, (![B_1479, A_1480]: (v4_pre_topc(B_1479, A_1480) | k2_pre_topc(A_1480, B_1479)!=B_1479 | ~v2_pre_topc(A_1480) | ~m1_subset_1(B_1479, k1_zfmisc_1(u1_struct_0(A_1480))) | ~l1_pre_topc(A_1480))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.25/6.23  tff(c_18789, plain, (![B_1479]: (v4_pre_topc(B_1479, '#skF_5') | k2_pre_topc('#skF_5', B_1479)!=B_1479 | ~v2_pre_topc('#skF_5') | ~m1_subset_1(B_1479, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_18786])).
% 14.25/6.23  tff(c_18834, plain, (![B_1484]: (v4_pre_topc(B_1484, '#skF_5') | k2_pre_topc('#skF_5', B_1484)!=B_1484 | ~m1_subset_1(B_1484, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_18789])).
% 14.25/6.23  tff(c_18837, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_14026, c_18834])).
% 14.25/6.23  tff(c_18851, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_18661, c_18837])).
% 14.25/6.23  tff(c_18903, plain, (k2_struct_0('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18896, c_18851])).
% 14.25/6.23  tff(c_22768, plain, (![A_1797, B_1798, C_1799]: (r2_hidden('#skF_2'(A_1797, B_1798, C_1799), u1_struct_0(A_1797)) | k2_pre_topc(A_1797, B_1798)=C_1799 | ~m1_subset_1(C_1799, k1_zfmisc_1(u1_struct_0(A_1797))) | ~m1_subset_1(B_1798, k1_zfmisc_1(u1_struct_0(A_1797))) | ~l1_pre_topc(A_1797))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_22776, plain, (![B_1798, C_1799]: (r2_hidden('#skF_2'('#skF_5', B_1798, C_1799), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1798)=C_1799 | ~m1_subset_1(C_1799, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1798, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_22768])).
% 14.25/6.23  tff(c_22784, plain, (![B_1803, C_1804]: (r2_hidden('#skF_2'('#skF_5', B_1803, C_1804), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1803)=C_1804 | ~m1_subset_1(C_1804, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1803, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14024, c_14024, c_22776])).
% 14.25/6.23  tff(c_14152, plain, (![A_1066, C_1067, B_1068]: (m1_subset_1(A_1066, C_1067) | ~m1_subset_1(B_1068, k1_zfmisc_1(C_1067)) | ~r2_hidden(A_1066, B_1068))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.25/6.23  tff(c_14163, plain, (![A_1066, A_12]: (m1_subset_1(A_1066, A_12) | ~r2_hidden(A_1066, A_12))), inference(resolution, [status(thm)], [c_115, c_14152])).
% 14.25/6.23  tff(c_22795, plain, (![B_1803, C_1804]: (m1_subset_1('#skF_2'('#skF_5', B_1803, C_1804), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1803)=C_1804 | ~m1_subset_1(C_1804, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1803, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_22784, c_14163])).
% 14.25/6.23  tff(c_84, plain, (![A_137]: (v3_pre_topc(k2_struct_0(A_137), A_137) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.25/6.23  tff(c_18679, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_18660])).
% 14.25/6.23  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.25/6.23  tff(c_14176, plain, (![A_1078, B_1079]: (k4_xboole_0(A_1078, B_1079)=k3_subset_1(A_1078, B_1079) | ~m1_subset_1(B_1079, k1_zfmisc_1(A_1078)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.25/6.23  tff(c_14188, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=k3_subset_1(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_14176])).
% 14.25/6.23  tff(c_14193, plain, (![A_17]: (k3_subset_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14188])).
% 14.25/6.23  tff(c_18724, plain, (![B_1475, A_1476]: (v4_pre_topc(B_1475, A_1476) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1476), B_1475), A_1476) | ~m1_subset_1(B_1475, k1_zfmisc_1(u1_struct_0(A_1476))) | ~l1_pre_topc(A_1476))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.25/6.23  tff(c_18728, plain, (![A_1476]: (v4_pre_topc(k1_xboole_0, A_1476) | ~v3_pre_topc(u1_struct_0(A_1476), A_1476) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1476))) | ~l1_pre_topc(A_1476))), inference(superposition, [status(thm), theory('equality')], [c_14193, c_18724])).
% 14.25/6.23  tff(c_18770, plain, (![A_1478]: (v4_pre_topc(k1_xboole_0, A_1478) | ~v3_pre_topc(u1_struct_0(A_1478), A_1478) | ~l1_pre_topc(A_1478))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18728])).
% 14.25/6.23  tff(c_18773, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14024, c_18770])).
% 14.25/6.23  tff(c_18775, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_18773])).
% 14.25/6.23  tff(c_18776, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_18679, c_18775])).
% 14.25/6.23  tff(c_18779, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_84, c_18776])).
% 14.25/6.23  tff(c_18783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_18779])).
% 14.25/6.23  tff(c_18784, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_18660])).
% 14.25/6.23  tff(c_18785, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_18660])).
% 14.25/6.23  tff(c_18861, plain, (![A_1485, B_1486]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_1485), B_1486), A_1485) | ~v4_pre_topc(B_1486, A_1485) | ~m1_subset_1(B_1486, k1_zfmisc_1(u1_struct_0(A_1485))) | ~l1_pre_topc(A_1485))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.25/6.23  tff(c_18865, plain, (![A_1485]: (v3_pre_topc(u1_struct_0(A_1485), A_1485) | ~v4_pre_topc(k1_xboole_0, A_1485) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1485))) | ~l1_pre_topc(A_1485))), inference(superposition, [status(thm), theory('equality')], [c_14193, c_18861])).
% 14.25/6.23  tff(c_18873, plain, (![A_1487]: (v3_pre_topc(u1_struct_0(A_1487), A_1487) | ~v4_pre_topc(k1_xboole_0, A_1487) | ~l1_pre_topc(A_1487))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18865])).
% 14.25/6.23  tff(c_18876, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14024, c_18873])).
% 14.25/6.23  tff(c_18878, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_18785, c_18876])).
% 14.25/6.23  tff(c_19011, plain, (![A_1499, B_1500, C_1501]: (r2_hidden('#skF_2'(A_1499, B_1500, C_1501), u1_struct_0(A_1499)) | k2_pre_topc(A_1499, B_1500)=C_1501 | ~m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0(A_1499))) | ~m1_subset_1(B_1500, k1_zfmisc_1(u1_struct_0(A_1499))) | ~l1_pre_topc(A_1499))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_19019, plain, (![B_1500, C_1501]: (r2_hidden('#skF_2'('#skF_5', B_1500, C_1501), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1500)=C_1501 | ~m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_19011])).
% 14.25/6.23  tff(c_19023, plain, (![B_1500, C_1501]: (r2_hidden('#skF_2'('#skF_5', B_1500, C_1501), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1500)=C_1501 | ~m1_subset_1(C_1501, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14024, c_14024, c_19019])).
% 14.25/6.23  tff(c_21259, plain, (![A_1726, B_1727, C_1728, E_1729]: (v3_pre_topc('#skF_3'(A_1726, B_1727, C_1728), A_1726) | ~r1_xboole_0(B_1727, E_1729) | ~r2_hidden('#skF_2'(A_1726, B_1727, C_1728), E_1729) | ~v3_pre_topc(E_1729, A_1726) | ~m1_subset_1(E_1729, k1_zfmisc_1(u1_struct_0(A_1726))) | k2_pre_topc(A_1726, B_1727)=C_1728 | ~m1_subset_1(C_1728, k1_zfmisc_1(u1_struct_0(A_1726))) | ~m1_subset_1(B_1727, k1_zfmisc_1(u1_struct_0(A_1726))) | ~l1_pre_topc(A_1726))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_21311, plain, (![B_1500, C_1501]: (v3_pre_topc('#skF_3'('#skF_5', B_1500, C_1501), '#skF_5') | ~r1_xboole_0(B_1500, k2_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1500)=C_1501 | ~m1_subset_1(C_1501, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_19023, c_21259])).
% 14.25/6.23  tff(c_21994, plain, (![B_1767, C_1768]: (v3_pre_topc('#skF_3'('#skF_5', B_1767, C_1768), '#skF_5') | ~r1_xboole_0(B_1767, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1767)=C_1768 | ~m1_subset_1(C_1768, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1767, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14024, c_14024, c_115, c_14024, c_18878, c_21311])).
% 14.25/6.23  tff(c_22026, plain, (![B_1769]: (v3_pre_topc('#skF_3'('#skF_5', B_1769, '#skF_6'), '#skF_5') | ~r1_xboole_0(B_1769, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1769)='#skF_6' | ~m1_subset_1(B_1769, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_14026, c_21994])).
% 14.25/6.23  tff(c_22058, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_6'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_22, c_22026])).
% 14.25/6.23  tff(c_22072, plain, (v3_pre_topc('#skF_3'('#skF_5', k1_xboole_0, '#skF_6'), '#skF_5') | ~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18784, c_22058])).
% 14.25/6.23  tff(c_22158, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_22072])).
% 14.25/6.23  tff(c_22162, plain, (k3_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_22158])).
% 14.25/6.23  tff(c_22166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13949, c_22162])).
% 14.25/6.23  tff(c_22168, plain, (r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_22072])).
% 14.25/6.23  tff(c_102, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_14019, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_102])).
% 14.25/6.23  tff(c_14025, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14024, c_14019])).
% 14.25/6.23  tff(c_14162, plain, (![A_1066]: (m1_subset_1(A_1066, k2_struct_0('#skF_5')) | ~r2_hidden(A_1066, '#skF_7'))), inference(resolution, [status(thm)], [c_14025, c_14152])).
% 14.25/6.23  tff(c_18997, plain, (![A_1496, C_1497, B_1498]: (~v2_struct_0(A_1496) | ~r2_hidden(C_1497, k2_pre_topc(A_1496, B_1498)) | ~m1_subset_1(C_1497, u1_struct_0(A_1496)) | ~m1_subset_1(B_1498, k1_zfmisc_1(u1_struct_0(A_1496))) | ~l1_pre_topc(A_1496))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.25/6.23  tff(c_19001, plain, (![C_1497]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1497, k1_xboole_0) | ~m1_subset_1(C_1497, u1_struct_0('#skF_5')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_18784, c_18997])).
% 14.25/6.23  tff(c_19007, plain, (![C_1497]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1497, k1_xboole_0) | ~m1_subset_1(C_1497, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_22, c_14024, c_14024, c_19001])).
% 14.25/6.23  tff(c_19010, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_19007])).
% 14.25/6.23  tff(c_74, plain, (![A_112, B_124, C_130]: (m1_subset_1('#skF_4'(A_112, B_124, C_130), k1_zfmisc_1(u1_struct_0(A_112))) | r2_hidden(C_130, k2_pre_topc(A_112, B_124)) | v2_struct_0(A_112) | ~m1_subset_1(C_130, u1_struct_0(A_112)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.25/6.23  tff(c_19053, plain, (![C_1512, A_1513, B_1514]: (r2_hidden(C_1512, '#skF_4'(A_1513, B_1514, C_1512)) | r2_hidden(C_1512, k2_pre_topc(A_1513, B_1514)) | v2_struct_0(A_1513) | ~m1_subset_1(C_1512, u1_struct_0(A_1513)) | ~m1_subset_1(B_1514, k1_zfmisc_1(u1_struct_0(A_1513))) | ~l1_pre_topc(A_1513))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.25/6.23  tff(c_19055, plain, (![C_1512, B_1514]: (r2_hidden(C_1512, '#skF_4'('#skF_5', B_1514, C_1512)) | r2_hidden(C_1512, k2_pre_topc('#skF_5', B_1514)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1512, u1_struct_0('#skF_5')) | ~m1_subset_1(B_1514, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_19053])).
% 14.25/6.23  tff(c_19063, plain, (![C_1512, B_1514]: (r2_hidden(C_1512, '#skF_4'('#skF_5', B_1514, C_1512)) | r2_hidden(C_1512, k2_pre_topc('#skF_5', B_1514)) | v2_struct_0('#skF_5') | ~m1_subset_1(C_1512, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1514, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14024, c_19055])).
% 14.25/6.23  tff(c_19102, plain, (![C_1520, B_1521]: (r2_hidden(C_1520, '#skF_4'('#skF_5', B_1521, C_1520)) | r2_hidden(C_1520, k2_pre_topc('#skF_5', B_1521)) | ~m1_subset_1(C_1520, k2_struct_0('#skF_5')) | ~m1_subset_1(B_1521, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_19010, c_19063])).
% 14.25/6.23  tff(c_19104, plain, (![C_1520]: (r2_hidden(C_1520, '#skF_4'('#skF_5', '#skF_6', C_1520)) | r2_hidden(C_1520, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1520, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_14026, c_19102])).
% 14.25/6.23  tff(c_19132, plain, (![C_1525]: (r2_hidden(C_1525, '#skF_4'('#skF_5', '#skF_6', C_1525)) | r2_hidden(C_1525, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1525, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_18896, c_19104])).
% 14.25/6.23  tff(c_19291, plain, (![C_1546, A_1547]: (r2_hidden(C_1546, A_1547) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_1546), k1_zfmisc_1(A_1547)) | r2_hidden(C_1546, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1546, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_19132, c_20])).
% 14.25/6.23  tff(c_19295, plain, (![C_130]: (r2_hidden(C_130, u1_struct_0('#skF_5')) | r2_hidden(C_130, k2_struct_0('#skF_5')) | ~m1_subset_1(C_130, k2_struct_0('#skF_5')) | r2_hidden(C_130, k2_pre_topc('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_130, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_19291])).
% 14.25/6.23  tff(c_19302, plain, (![C_130]: (r2_hidden(C_130, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(C_130, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14026, c_14024, c_14024, c_18896, c_14024, c_19295])).
% 14.25/6.23  tff(c_19303, plain, (![C_130]: (r2_hidden(C_130, k2_struct_0('#skF_5')) | ~m1_subset_1(C_130, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_19010, c_19302])).
% 14.25/6.23  tff(c_98, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_13927, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_98])).
% 14.25/6.23  tff(c_96, plain, (r1_xboole_0('#skF_6', '#skF_7') | ~v1_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_178])).
% 14.25/6.23  tff(c_14014, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_96])).
% 14.25/6.23  tff(c_19527, plain, (![B_1582, D_1583, C_1584, A_1585]: (~r1_xboole_0(B_1582, D_1583) | ~r2_hidden(C_1584, D_1583) | ~v3_pre_topc(D_1583, A_1585) | ~m1_subset_1(D_1583, k1_zfmisc_1(u1_struct_0(A_1585))) | ~r2_hidden(C_1584, k2_pre_topc(A_1585, B_1582)) | ~m1_subset_1(C_1584, u1_struct_0(A_1585)) | ~m1_subset_1(B_1582, k1_zfmisc_1(u1_struct_0(A_1585))) | ~l1_pre_topc(A_1585))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.25/6.23  tff(c_19569, plain, (![C_1590, A_1591]: (~r2_hidden(C_1590, '#skF_7') | ~v3_pre_topc('#skF_7', A_1591) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_1591))) | ~r2_hidden(C_1590, k2_pre_topc(A_1591, '#skF_6')) | ~m1_subset_1(C_1590, u1_struct_0(A_1591)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1591))) | ~l1_pre_topc(A_1591))), inference(resolution, [status(thm)], [c_14014, c_19527])).
% 14.25/6.23  tff(c_19571, plain, (![C_1590]: (~r2_hidden(C_1590, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden(C_1590, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_1590, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14024, c_19569])).
% 14.25/6.23  tff(c_19574, plain, (![C_1592]: (~r2_hidden(C_1592, '#skF_7') | ~r2_hidden(C_1592, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1592, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14026, c_14024, c_14024, c_18896, c_14025, c_13927, c_19571])).
% 14.25/6.23  tff(c_19583, plain, (![C_1593]: (~r2_hidden(C_1593, '#skF_7') | ~m1_subset_1(C_1593, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_19303, c_19574])).
% 14.25/6.23  tff(c_19594, plain, (![A_1066]: (~r2_hidden(A_1066, '#skF_7'))), inference(resolution, [status(thm)], [c_14162, c_19583])).
% 14.25/6.23  tff(c_21458, plain, (![A_1744, B_1745, C_1746, E_1747]: (r2_hidden('#skF_2'(A_1744, B_1745, C_1746), C_1746) | ~r1_xboole_0(B_1745, E_1747) | ~r2_hidden('#skF_2'(A_1744, B_1745, C_1746), E_1747) | ~v3_pre_topc(E_1747, A_1744) | ~m1_subset_1(E_1747, k1_zfmisc_1(u1_struct_0(A_1744))) | k2_pre_topc(A_1744, B_1745)=C_1746 | ~m1_subset_1(C_1746, k1_zfmisc_1(u1_struct_0(A_1744))) | ~m1_subset_1(B_1745, k1_zfmisc_1(u1_struct_0(A_1744))) | ~l1_pre_topc(A_1744))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.23  tff(c_21510, plain, (![B_1500, C_1501]: (r2_hidden('#skF_2'('#skF_5', B_1500, C_1501), C_1501) | ~r1_xboole_0(B_1500, k2_struct_0('#skF_5')) | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_1501, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1500)=C_1501 | ~m1_subset_1(C_1501, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1500, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_19023, c_21458])).
% 14.25/6.23  tff(c_22668, plain, (![B_1793, C_1794]: (r2_hidden('#skF_2'('#skF_5', B_1793, C_1794), C_1794) | ~r1_xboole_0(B_1793, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1793)=C_1794 | ~m1_subset_1(C_1794, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1793, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14024, c_14024, c_115, c_14024, c_18878, c_21510])).
% 14.25/6.23  tff(c_22684, plain, (![B_1793]: (r2_hidden('#skF_2'('#skF_5', B_1793, '#skF_7'), '#skF_7') | ~r1_xboole_0(B_1793, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1793)='#skF_7' | ~m1_subset_1(B_1793, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_14025, c_22668])).
% 14.25/6.23  tff(c_22702, plain, (![B_1795]: (~r1_xboole_0(B_1795, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1795)='#skF_7' | ~m1_subset_1(B_1795, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_19594, c_22684])).
% 14.25/6.23  tff(c_22734, plain, (~r1_xboole_0(k1_xboole_0, k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_22, c_22702])).
% 14.25/6.23  tff(c_22748, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_18784, c_22168, c_22734])).
% 14.25/6.23  tff(c_22750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13924, c_22748])).
% 14.25/6.23  tff(c_22752, plain, (v2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_19007])).
% 14.25/6.23  tff(c_18999, plain, (![C_1497]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1497, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1497, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_18896, c_18997])).
% 14.25/6.23  tff(c_19005, plain, (![C_1497]: (~v2_struct_0('#skF_5') | ~r2_hidden(C_1497, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1497, k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_14026, c_14024, c_14024, c_18999])).
% 14.25/6.23  tff(c_22753, plain, (~v2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_19005])).
% 14.25/6.23  tff(c_22755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22752, c_22753])).
% 14.25/6.23  tff(c_22756, plain, (![C_1497]: (~r2_hidden(C_1497, k2_struct_0('#skF_5')) | ~m1_subset_1(C_1497, k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_19005])).
% 14.25/6.23  tff(c_22804, plain, (![B_1809, C_1810]: (~m1_subset_1('#skF_2'('#skF_5', B_1809, C_1810), k2_struct_0('#skF_5')) | k2_pre_topc('#skF_5', B_1809)=C_1810 | ~m1_subset_1(C_1810, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1809, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_22784, c_22756])).
% 14.25/6.23  tff(c_22817, plain, (![B_1811, C_1812]: (k2_pre_topc('#skF_5', B_1811)=C_1812 | ~m1_subset_1(C_1812, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_1811, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_22795, c_22804])).
% 14.25/6.23  tff(c_22845, plain, (![B_1816]: (k2_pre_topc('#skF_5', B_1816)='#skF_6' | ~m1_subset_1(B_1816, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_14026, c_22817])).
% 14.25/6.23  tff(c_22860, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_14026, c_22845])).
% 14.25/6.23  tff(c_22864, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22860, c_18896])).
% 14.25/6.23  tff(c_22866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18903, c_22864])).
% 14.25/6.23  tff(c_22867, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_18655])).
% 14.25/6.23  tff(c_22931, plain, (![B_1822]: (k2_pre_topc('#skF_5', B_1822)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1822, '#skF_5') | ~m1_subset_1(B_1822, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_18615])).
% 14.25/6.23  tff(c_22934, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_14026, c_22931])).
% 14.25/6.23  tff(c_22948, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_22867, c_22934])).
% 14.25/6.23  tff(c_22998, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22948, c_84])).
% 14.25/6.23  tff(c_23002, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_22998])).
% 14.25/6.23  tff(c_22988, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22948, c_14024])).
% 14.25/6.23  tff(c_23061, plain, (![B_1825, A_1826]: (v4_pre_topc(B_1825, A_1826) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1826), B_1825), A_1826) | ~m1_subset_1(B_1825, k1_zfmisc_1(u1_struct_0(A_1826))) | ~l1_pre_topc(A_1826))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.25/6.24  tff(c_23068, plain, (![A_1826]: (v4_pre_topc(k1_xboole_0, A_1826) | ~v3_pre_topc(u1_struct_0(A_1826), A_1826) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1826))) | ~l1_pre_topc(A_1826))), inference(superposition, [status(thm), theory('equality')], [c_14193, c_23061])).
% 14.25/6.24  tff(c_23097, plain, (![A_1829]: (v4_pre_topc(k1_xboole_0, A_1829) | ~v3_pre_topc(u1_struct_0(A_1829), A_1829) | ~l1_pre_topc(A_1829))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_23068])).
% 14.25/6.24  tff(c_23100, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22988, c_23097])).
% 14.25/6.24  tff(c_23102, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23002, c_23100])).
% 14.25/6.24  tff(c_23104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22874, c_23102])).
% 14.25/6.24  tff(c_23105, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_18660])).
% 14.25/6.24  tff(c_23538, plain, (![B_1861]: (k2_pre_topc('#skF_5', B_1861)=k2_struct_0('#skF_5') | ~v1_tops_1(B_1861, '#skF_5') | ~m1_subset_1(B_1861, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_18615])).
% 14.25/6.24  tff(c_23541, plain, (k2_pre_topc('#skF_5', '#skF_6')=k2_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_14026, c_23538])).
% 14.25/6.24  tff(c_23555, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13925, c_22867, c_23541])).
% 14.25/6.24  tff(c_23579, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_23555, c_14025])).
% 14.25/6.24  tff(c_23580, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23555, c_14024])).
% 14.25/6.24  tff(c_23802, plain, (![A_1874, B_1875, C_1876]: (r2_hidden('#skF_2'(A_1874, B_1875, C_1876), u1_struct_0(A_1874)) | k2_pre_topc(A_1874, B_1875)=C_1876 | ~m1_subset_1(C_1876, k1_zfmisc_1(u1_struct_0(A_1874))) | ~m1_subset_1(B_1875, k1_zfmisc_1(u1_struct_0(A_1874))) | ~l1_pre_topc(A_1874))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.24  tff(c_23810, plain, (![B_1875, C_1876]: (r2_hidden('#skF_2'('#skF_5', B_1875, C_1876), '#skF_6') | k2_pre_topc('#skF_5', B_1875)=C_1876 | ~m1_subset_1(C_1876, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1875, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_23580, c_23802])).
% 14.25/6.24  tff(c_23831, plain, (![B_1878, C_1879]: (r2_hidden('#skF_2'('#skF_5', B_1878, C_1879), '#skF_6') | k2_pre_topc('#skF_5', B_1878)=C_1879 | ~m1_subset_1(C_1879, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_1878, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23580, c_23580, c_23810])).
% 14.25/6.24  tff(c_23837, plain, (![B_1878, C_1879, A_13]: (r2_hidden('#skF_2'('#skF_5', B_1878, C_1879), A_13) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_13)) | k2_pre_topc('#skF_5', B_1878)=C_1879 | ~m1_subset_1(C_1879, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_1878, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_23831, c_20])).
% 14.25/6.24  tff(c_23590, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_23555, c_84])).
% 14.25/6.24  tff(c_23594, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_23590])).
% 14.25/6.24  tff(c_23814, plain, (![B_1875, C_1876]: (r2_hidden('#skF_2'('#skF_5', B_1875, C_1876), '#skF_6') | k2_pre_topc('#skF_5', B_1875)=C_1876 | ~m1_subset_1(C_1876, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_1875, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23580, c_23580, c_23810])).
% 14.25/6.24  tff(c_26408, plain, (![A_2111, B_2112, C_2113, E_2114]: (r2_hidden('#skF_2'(A_2111, B_2112, C_2113), C_2113) | ~r1_xboole_0(B_2112, E_2114) | ~r2_hidden('#skF_2'(A_2111, B_2112, C_2113), E_2114) | ~v3_pre_topc(E_2114, A_2111) | ~m1_subset_1(E_2114, k1_zfmisc_1(u1_struct_0(A_2111))) | k2_pre_topc(A_2111, B_2112)=C_2113 | ~m1_subset_1(C_2113, k1_zfmisc_1(u1_struct_0(A_2111))) | ~m1_subset_1(B_2112, k1_zfmisc_1(u1_struct_0(A_2111))) | ~l1_pre_topc(A_2111))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.24  tff(c_26471, plain, (![B_1875, C_1876]: (r2_hidden('#skF_2'('#skF_5', B_1875, C_1876), C_1876) | ~r1_xboole_0(B_1875, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_1876, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1875, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | k2_pre_topc('#skF_5', B_1875)=C_1876 | ~m1_subset_1(C_1876, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_1875, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_23814, c_26408])).
% 14.25/6.24  tff(c_26582, plain, (![B_2123, C_2124]: (r2_hidden('#skF_2'('#skF_5', B_2123, C_2124), C_2124) | ~r1_xboole_0(B_2123, '#skF_6') | k2_pre_topc('#skF_5', B_2123)=C_2124 | ~m1_subset_1(C_2124, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_2123, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23580, c_23580, c_115, c_23580, c_23594, c_26471])).
% 14.25/6.24  tff(c_25751, plain, (![B_2079, E_2080, D_2081, A_2082]: (~r1_xboole_0(B_2079, E_2080) | ~r2_hidden(D_2081, E_2080) | ~v3_pre_topc(E_2080, A_2082) | ~m1_subset_1(E_2080, k1_zfmisc_1(u1_struct_0(A_2082))) | ~r2_hidden(D_2081, k2_pre_topc(A_2082, B_2079)) | ~r2_hidden(D_2081, u1_struct_0(A_2082)) | ~m1_subset_1(k2_pre_topc(A_2082, B_2079), k1_zfmisc_1(u1_struct_0(A_2082))) | ~m1_subset_1(B_2079, k1_zfmisc_1(u1_struct_0(A_2082))) | ~l1_pre_topc(A_2082))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.25/6.24  tff(c_25808, plain, (![D_2086, A_2087]: (~r2_hidden(D_2086, '#skF_7') | ~v3_pre_topc('#skF_7', A_2087) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_2087))) | ~r2_hidden(D_2086, k2_pre_topc(A_2087, '#skF_6')) | ~r2_hidden(D_2086, u1_struct_0(A_2087)) | ~m1_subset_1(k2_pre_topc(A_2087, '#skF_6'), k1_zfmisc_1(u1_struct_0(A_2087))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_2087))) | ~l1_pre_topc(A_2087))), inference(resolution, [status(thm)], [c_14014, c_25751])).
% 14.25/6.24  tff(c_25828, plain, (![D_2086]: (~r2_hidden(D_2086, '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(D_2086, '#skF_6') | ~r2_hidden(D_2086, u1_struct_0('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22867, c_25808])).
% 14.25/6.24  tff(c_25846, plain, (![D_2086]: (~r2_hidden(D_2086, '#skF_7') | ~r2_hidden(D_2086, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_115, c_23580, c_115, c_23580, c_22867, c_23580, c_23579, c_23580, c_13927, c_25828])).
% 14.25/6.24  tff(c_26595, plain, (![B_2123]: (~r2_hidden('#skF_2'('#skF_5', B_2123, '#skF_7'), '#skF_6') | ~r1_xboole_0(B_2123, '#skF_6') | k2_pre_topc('#skF_5', B_2123)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_2123, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_26582, c_25846])).
% 14.25/6.24  tff(c_26669, plain, (![B_2125]: (~r2_hidden('#skF_2'('#skF_5', B_2125, '#skF_7'), '#skF_6') | ~r1_xboole_0(B_2125, '#skF_6') | k2_pre_topc('#skF_5', B_2125)='#skF_7' | ~m1_subset_1(B_2125, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_23579, c_26595])).
% 14.25/6.24  tff(c_26677, plain, (![B_1878]: (~r1_xboole_0(B_1878, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | k2_pre_topc('#skF_5', B_1878)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_1878, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_23837, c_26669])).
% 14.25/6.24  tff(c_26689, plain, (![B_2126]: (~r1_xboole_0(B_2126, '#skF_6') | k2_pre_topc('#skF_5', B_2126)='#skF_7' | ~m1_subset_1(B_2126, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_23579, c_115, c_26677])).
% 14.25/6.24  tff(c_26717, plain, (~r1_xboole_0(k1_xboole_0, '#skF_6') | k2_pre_topc('#skF_5', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_22, c_26689])).
% 14.25/6.24  tff(c_26729, plain, (~r1_xboole_0(k1_xboole_0, '#skF_6') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_23105, c_26717])).
% 14.25/6.24  tff(c_26730, plain, (~r1_xboole_0(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_13924, c_26729])).
% 14.25/6.24  tff(c_26733, plain, (k3_xboole_0(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_26730])).
% 14.25/6.24  tff(c_26737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13949, c_26733])).
% 14.25/6.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.25/6.24  
% 14.25/6.24  Inference rules
% 14.25/6.24  ----------------------
% 14.25/6.24  #Ref     : 0
% 14.25/6.24  #Sup     : 5595
% 14.25/6.24  #Fact    : 12
% 14.25/6.24  #Define  : 0
% 14.25/6.24  #Split   : 131
% 14.25/6.24  #Chain   : 0
% 14.25/6.24  #Close   : 0
% 14.25/6.24  
% 14.25/6.24  Ordering : KBO
% 14.25/6.24  
% 14.25/6.24  Simplification rules
% 14.25/6.24  ----------------------
% 14.25/6.24  #Subsume      : 1065
% 14.25/6.24  #Demod        : 5944
% 14.25/6.24  #Tautology    : 1310
% 14.25/6.24  #SimpNegUnit  : 531
% 14.25/6.24  #BackRed      : 345
% 14.25/6.24  
% 14.25/6.24  #Partial instantiations: 0
% 14.25/6.24  #Strategies tried      : 1
% 14.25/6.24  
% 14.25/6.24  Timing (in seconds)
% 14.25/6.24  ----------------------
% 14.25/6.24  Preprocessing        : 0.42
% 14.25/6.24  Parsing              : 0.21
% 14.25/6.24  CNF conversion       : 0.04
% 14.25/6.24  Main loop            : 4.90
% 14.25/6.24  Inferencing          : 1.42
% 14.25/6.24  Reduction            : 1.67
% 14.25/6.24  Demodulation         : 1.18
% 14.25/6.24  BG Simplification    : 0.13
% 14.25/6.24  Subsumption          : 1.34
% 14.25/6.24  Abstraction          : 0.17
% 14.25/6.24  MUC search           : 0.00
% 14.25/6.24  Cooper               : 0.00
% 14.25/6.24  Total                : 5.40
% 14.25/6.24  Index Insertion      : 0.00
% 14.25/6.24  Index Deletion       : 0.00
% 14.25/6.24  Index Matching       : 0.00
% 14.25/6.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
