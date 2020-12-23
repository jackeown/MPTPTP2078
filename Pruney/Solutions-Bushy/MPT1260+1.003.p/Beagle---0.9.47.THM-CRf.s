%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1260+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:40 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 474 expanded)
%              Number of leaves         :   34 ( 170 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 (1017 expanded)
%              Number of equality atoms :   61 ( 266 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_83,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_117,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_843,plain,(
    ! [A_126,B_127,C_128] :
      ( k7_subset_1(A_126,B_127,C_128) = k4_xboole_0(B_127,C_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_867,plain,(
    ! [C_128] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_128) = k4_xboole_0('#skF_2',C_128) ),
    inference(resolution,[status(thm)],[c_42,c_843])).

tff(c_2037,plain,(
    ! [A_189,B_190] :
      ( k7_subset_1(u1_struct_0(A_189),B_190,k2_tops_1(A_189,B_190)) = k1_tops_1(A_189,B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2078,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2037])).

tff(c_2112,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_867,c_2078])).

tff(c_26,plain,(
    ! [A_29,B_30] : k6_subset_1(A_29,B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_124,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_135,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_subset_1(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_55,c_124])).

tff(c_868,plain,(
    ! [C_129] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_129) = k4_xboole_0('#skF_2',C_129) ),
    inference(resolution,[status(thm)],[c_42,c_843])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_877,plain,(
    ! [C_129] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_129),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_14])).

tff(c_937,plain,(
    ! [C_133] : m1_subset_1(k4_xboole_0('#skF_2',C_133),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_877])).

tff(c_953,plain,(
    ! [B_13] : m1_subset_1(k3_subset_1('#skF_2',k4_xboole_0('#skF_2',B_13)),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_937])).

tff(c_2146,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_953])).

tff(c_36,plain,(
    ! [C_51,A_39,D_53,B_47] :
      ( v3_pre_topc(C_51,A_39)
      | k1_tops_1(A_39,C_51) != C_51
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(B_47)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(B_47)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2424,plain,(
    ! [D_197,B_198] :
      ( ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0(B_198)))
      | ~ l1_pre_topc(B_198) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2427,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2146,c_2424])).

tff(c_2482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2427])).

tff(c_2675,plain,(
    ! [C_199,A_200] :
      ( v3_pre_topc(C_199,A_200)
      | k1_tops_1(A_200,C_199) != C_199
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2739,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2675])).

tff(c_2778,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2739])).

tff(c_2779,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_2778])).

tff(c_887,plain,(
    ! [B_130,A_131] :
      ( r1_tarski(B_130,k2_pre_topc(A_131,B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_907,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_887])).

tff(c_923,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_907])).

tff(c_777,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k2_pre_topc(A_121,B_122),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_175,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_54])).

tff(c_289,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1(k7_subset_1(A_83,B_84,C_85),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_300,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_289])).

tff(c_392,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_784,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_777,c_392])).

tff(c_798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_784])).

tff(c_800,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_1724,plain,(
    ! [C_181] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_181) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_181) ),
    inference(resolution,[status(thm)],[c_800,c_843])).

tff(c_1736,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_175])).

tff(c_32,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_134,plain,(
    ! [B_35,A_34] :
      ( k4_xboole_0(B_35,A_34) = k3_subset_1(B_35,A_34)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_124])).

tff(c_927,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_923,c_134])).

tff(c_1763,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1736,c_927])).

tff(c_147,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,(
    ! [B_35,A_34] :
      ( k3_subset_1(B_35,k3_subset_1(B_35,A_34)) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_1867,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_154])).

tff(c_1871,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_1867])).

tff(c_861,plain,(
    ! [C_128] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_128) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_128) ),
    inference(resolution,[status(thm)],[c_800,c_843])).

tff(c_2276,plain,(
    ! [A_192,B_193] :
      ( k7_subset_1(u1_struct_0(A_192),k2_pre_topc(A_192,B_193),k1_tops_1(A_192,B_193)) = k2_tops_1(A_192,B_193)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2296,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_2276])).

tff(c_2302,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2296])).

tff(c_1205,plain,(
    ! [A_148,B_149,C_150] : k7_subset_1(A_148,k4_xboole_0(A_148,B_149),C_150) = k4_xboole_0(k4_xboole_0(A_148,B_149),C_150) ),
    inference(resolution,[status(thm)],[c_55,c_843])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_303,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(k7_subset_1(A_83,B_84,C_85),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_289,c_30])).

tff(c_1211,plain,(
    ! [A_148,B_149,C_150] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(A_148,B_149),C_150),A_148)
      | ~ m1_subset_1(k4_xboole_0(A_148,B_149),k1_zfmisc_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_303])).

tff(c_1258,plain,(
    ! [A_153,B_154,C_155] : r1_tarski(k4_xboole_0(k4_xboole_0(A_153,B_154),C_155),A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1211])).

tff(c_1269,plain,(
    ! [A_12,B_13,C_155] : r1_tarski(k4_xboole_0(k3_subset_1(A_12,k4_xboole_0(A_12,B_13)),C_155),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1258])).

tff(c_2608,plain,(
    ! [C_155] : r1_tarski(k4_xboole_0(k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')),C_155),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2302,c_1269])).

tff(c_2780,plain,(
    ! [C_201] : r1_tarski(k4_xboole_0('#skF_2',C_201),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_2608])).

tff(c_2789,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_2780])).

tff(c_1214,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k4_xboole_0(k4_xboole_0(A_148,B_149),C_150),k1_zfmisc_1(A_148))
      | ~ m1_subset_1(k4_xboole_0(A_148,B_149),k1_zfmisc_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_14])).

tff(c_1284,plain,(
    ! [A_156,B_157,C_158] : m1_subset_1(k4_xboole_0(k4_xboole_0(A_156,B_157),C_158),k1_zfmisc_1(A_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1214])).

tff(c_1303,plain,(
    ! [A_12,B_13,C_158] : m1_subset_1(k4_xboole_0(k3_subset_1(A_12,k4_xboole_0(A_12,B_13)),C_158),k1_zfmisc_1(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1284])).

tff(c_2605,plain,(
    ! [C_158] : m1_subset_1(k4_xboole_0(k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')),C_158),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2302,c_1303])).

tff(c_2891,plain,(
    ! [C_203] : m1_subset_1(k4_xboole_0('#skF_2',C_203),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_2605])).

tff(c_2907,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_2891])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2927,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2907,c_4])).

tff(c_2935,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_2927])).

tff(c_3329,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2935,c_154])).

tff(c_3333,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_1871,c_3329])).

tff(c_3335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2779,c_3333])).

tff(c_3336,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3337,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3468,plain,(
    ! [A_226,B_227,C_228] :
      ( k7_subset_1(A_226,B_227,C_228) = k4_xboole_0(B_227,C_228)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3483,plain,(
    ! [C_228] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_228) = k4_xboole_0('#skF_2',C_228) ),
    inference(resolution,[status(thm)],[c_42,c_3468])).

tff(c_4802,plain,(
    ! [A_315,B_316] :
      ( k7_subset_1(u1_struct_0(A_315),B_316,k2_tops_1(A_315,B_316)) = k1_tops_1(A_315,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4841,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_4802])).

tff(c_4872,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3483,c_4841])).

tff(c_3392,plain,(
    ! [A_219,B_220] :
      ( k4_xboole_0(A_219,B_220) = k3_subset_1(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3532,plain,(
    ! [A_235,B_236] : k4_xboole_0(A_235,k4_xboole_0(A_235,B_236)) = k3_subset_1(A_235,k4_xboole_0(A_235,B_236)) ),
    inference(resolution,[status(thm)],[c_55,c_3392])).

tff(c_3484,plain,(
    ! [C_229] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_229) = k4_xboole_0('#skF_2',C_229) ),
    inference(resolution,[status(thm)],[c_42,c_3468])).

tff(c_3490,plain,(
    ! [C_229] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_229),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3484,c_14])).

tff(c_3496,plain,(
    ! [C_229] : m1_subset_1(k4_xboole_0('#skF_2',C_229),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3490])).

tff(c_3546,plain,(
    ! [B_236] : m1_subset_1(k3_subset_1('#skF_2',k4_xboole_0('#skF_2',B_236)),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3532,c_3496])).

tff(c_4926,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4872,c_3546])).

tff(c_38,plain,(
    ! [B_47,D_53,C_51,A_39] :
      ( k1_tops_1(B_47,D_53) = D_53
      | ~ v3_pre_topc(D_53,B_47)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(B_47)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(B_47)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5207,plain,(
    ! [C_323,A_324] :
      ( ~ m1_subset_1(C_323,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_5210,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4926,c_5207])).

tff(c_5268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_5210])).

tff(c_5464,plain,(
    ! [B_327,D_328] :
      ( k1_tops_1(B_327,D_328) = D_328
      | ~ v3_pre_topc(D_328,B_327)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(u1_struct_0(B_327)))
      | ~ l1_pre_topc(B_327) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_5528,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_5464])).

tff(c_5567,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3337,c_5528])).

tff(c_22,plain,(
    ! [A_23,B_25] :
      ( k7_subset_1(u1_struct_0(A_23),k2_pre_topc(A_23,B_25),k1_tops_1(A_23,B_25)) = k2_tops_1(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5604,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5567,c_22])).

tff(c_5611,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5604])).

tff(c_5613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3336,c_5611])).

%------------------------------------------------------------------------------
