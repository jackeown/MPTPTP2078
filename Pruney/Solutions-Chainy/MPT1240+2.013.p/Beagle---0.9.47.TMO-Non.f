%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:47 EST 2020

% Result     : Timeout 57.71s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  145 ( 364 expanded)
%              Number of leaves         :   36 ( 136 expanded)
%              Depth                    :   16
%              Number of atoms          :  292 (1054 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_66,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_65,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_155665,plain,(
    ! [A_2915,B_2916] :
      ( v3_pre_topc(k1_tops_1(A_2915,B_2916),A_2915)
      | ~ m1_subset_1(B_2916,k1_zfmisc_1(u1_struct_0(A_2915)))
      | ~ l1_pre_topc(A_2915)
      | ~ v2_pre_topc(A_2915) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_155670,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_155665])).

tff(c_155674,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_155670])).

tff(c_155529,plain,(
    ! [A_2905,B_2906] :
      ( r1_tarski(k1_tops_1(A_2905,B_2906),B_2906)
      | ~ m1_subset_1(B_2906,k1_zfmisc_1(u1_struct_0(A_2905)))
      | ~ l1_pre_topc(A_2905) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_155534,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_155529])).

tff(c_155538,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_155534])).

tff(c_154640,plain,(
    ! [A_2845,B_2846] :
      ( v3_pre_topc(k1_tops_1(A_2845,B_2846),A_2845)
      | ~ m1_subset_1(B_2846,k1_zfmisc_1(u1_struct_0(A_2845)))
      | ~ l1_pre_topc(A_2845)
      | ~ v2_pre_topc(A_2845) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_154647,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_154640])).

tff(c_154652,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_154647])).

tff(c_154354,plain,(
    ! [A_2824,B_2825] :
      ( r1_tarski(k1_tops_1(A_2824,B_2825),B_2825)
      | ~ m1_subset_1(B_2825,k1_zfmisc_1(u1_struct_0(A_2824)))
      | ~ l1_pre_topc(A_2824) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_154359,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_154354])).

tff(c_154363,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_154359])).

tff(c_153142,plain,(
    ! [A_2743,B_2744] :
      ( v3_pre_topc(k1_tops_1(A_2743,B_2744),A_2743)
      | ~ m1_subset_1(B_2744,k1_zfmisc_1(u1_struct_0(A_2743)))
      | ~ l1_pre_topc(A_2743)
      | ~ v2_pre_topc(A_2743) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_153147,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_153142])).

tff(c_153151,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_153147])).

tff(c_153029,plain,(
    ! [A_2735,B_2736] :
      ( r1_tarski(k1_tops_1(A_2735,B_2736),B_2736)
      | ~ m1_subset_1(B_2736,k1_zfmisc_1(u1_struct_0(A_2735)))
      | ~ l1_pre_topc(A_2735) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_153034,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_153029])).

tff(c_153038,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_153034])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_116,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_107,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_62,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_216,plain,(
    ! [A_75,B_76] :
      ( k3_subset_1(A_75,k3_subset_1(A_75,B_76)) = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_223,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_117,c_216])).

tff(c_149,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k3_subset_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_149])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_197,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_224,plain,(
    ! [B_15,A_14] :
      ( k3_subset_1(B_15,k3_subset_1(B_15,A_14)) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_216])).

tff(c_795,plain,(
    ! [A_112,B_113] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_112),B_113),A_112)
      | ~ v3_pre_topc(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_61962,plain,(
    ! [A_1390,A_1391] :
      ( v4_pre_topc(A_1390,A_1391)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1391),A_1390),A_1391)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_1391),A_1390),k1_zfmisc_1(u1_struct_0(A_1391)))
      | ~ l1_pre_topc(A_1391)
      | ~ r1_tarski(A_1390,u1_struct_0(A_1391)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_795])).

tff(c_61987,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')),'#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_61962])).

tff(c_62007,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_40,c_117,c_116,c_223,c_61987])).

tff(c_404,plain,(
    ! [A_84,B_85] :
      ( k2_pre_topc(A_84,B_85) = B_85
      | ~ v4_pre_topc(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1605,plain,(
    ! [A_158,A_159] :
      ( k2_pre_topc(A_158,A_159) = A_159
      | ~ v4_pre_topc(A_159,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ r1_tarski(A_159,u1_struct_0(A_158)) ) ),
    inference(resolution,[status(thm)],[c_18,c_404])).

tff(c_57648,plain,(
    ! [A_1281,B_1282] :
      ( k2_pre_topc(A_1281,k4_xboole_0(u1_struct_0(A_1281),B_1282)) = k4_xboole_0(u1_struct_0(A_1281),B_1282)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(A_1281),B_1282),A_1281)
      | ~ l1_pre_topc(A_1281) ) ),
    inference(resolution,[status(thm)],[c_6,c_1605])).

tff(c_57674,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(u1_struct_0('#skF_1'),'#skF_4')) = k4_xboole_0(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_57648])).

tff(c_57690,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_159,c_159,c_57674])).

tff(c_92824,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62007,c_57690])).

tff(c_1135,plain,(
    ! [A_133,B_134] :
      ( k3_subset_1(u1_struct_0(A_133),k2_pre_topc(A_133,k3_subset_1(u1_struct_0(A_133),B_134))) = k1_tops_1(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_63902,plain,(
    ! [A_1440,A_1441] :
      ( k3_subset_1(u1_struct_0(A_1440),k2_pre_topc(A_1440,A_1441)) = k1_tops_1(A_1440,k3_subset_1(u1_struct_0(A_1440),A_1441))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_1440),A_1441),k1_zfmisc_1(u1_struct_0(A_1440)))
      | ~ l1_pre_topc(A_1440)
      | ~ r1_tarski(A_1441,u1_struct_0(A_1440)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_1135])).

tff(c_63927,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'))) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_63902])).

tff(c_63945,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'))) = k1_tops_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_40,c_117,c_223,c_63927])).

tff(c_92825,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92824,c_63945])).

tff(c_92826,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_92825])).

tff(c_36,plain,(
    ! [A_32,B_36,C_38] :
      ( r1_tarski(k1_tops_1(A_32,B_36),k1_tops_1(A_32,C_38))
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_93167,plain,(
    ! [C_38] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_38))
      | ~ r1_tarski('#skF_4',C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92826,c_36])).

tff(c_152407,plain,(
    ! [C_2703] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_2703))
      | ~ r1_tarski('#skF_4',C_2703)
      | ~ m1_subset_1(C_2703,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_117,c_93167])).

tff(c_152427,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_152407])).

tff(c_152439,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_152427])).

tff(c_98,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(k1_tarski(A_70),B_71) = B_71
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    ! [A_70,C_3,B_71] :
      ( r1_tarski(k1_tarski(A_70),C_3)
      | ~ r1_tarski(B_71,C_3)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_2])).

tff(c_152668,plain,(
    ! [A_2707] :
      ( r1_tarski(k1_tarski(A_2707),k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_2707,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152439,c_170])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152721,plain,(
    ! [A_2708] :
      ( r2_hidden(A_2708,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_2708,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_152668,c_8])).

tff(c_44,plain,(
    ! [D_47] :
      ( ~ r2_hidden('#skF_2',D_47)
      | ~ r1_tarski(D_47,'#skF_3')
      | ~ v3_pre_topc(D_47,'#skF_1')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_549,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_152741,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_152721,c_549])).

tff(c_152758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_152741])).

tff(c_152761,plain,(
    ! [D_2709] :
      ( ~ r2_hidden('#skF_2',D_2709)
      | ~ r1_tarski(D_2709,'#skF_3')
      | ~ v3_pre_topc(D_2709,'#skF_1')
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_152768,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_117,c_152761])).

tff(c_152782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_107,c_84,c_152768])).

tff(c_152784,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_152788,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_152784])).

tff(c_111,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_152789,plain,(
    ! [A_2710,C_2711,B_2712] :
      ( r1_tarski(A_2710,C_2711)
      | ~ r1_tarski(k2_xboole_0(A_2710,B_2712),C_2711) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152799,plain,(
    ! [C_2713] :
      ( r1_tarski('#skF_4',C_2713)
      | ~ r1_tarski('#skF_3',C_2713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_152789])).

tff(c_152802,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_73,c_152799])).

tff(c_152806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152788,c_152802])).

tff(c_152807,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_153046,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_153038,c_4])).

tff(c_153050,plain,(
    ! [C_3] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_3)
      | ~ r1_tarski('#skF_3',C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153046,c_2])).

tff(c_152808,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_47] :
      ( ~ r2_hidden('#skF_2',D_47)
      | ~ r1_tarski(D_47,'#skF_3')
      | ~ v3_pre_topc(D_47,'#skF_1')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_152882,plain,(
    ! [D_2727] :
      ( ~ r2_hidden('#skF_2',D_2727)
      | ~ r1_tarski(D_2727,'#skF_3')
      | ~ v3_pre_topc(D_2727,'#skF_1')
      | ~ m1_subset_1(D_2727,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152808,c_56])).

tff(c_154064,plain,(
    ! [A_2798] :
      ( ~ r2_hidden('#skF_2',A_2798)
      | ~ r1_tarski(A_2798,'#skF_3')
      | ~ v3_pre_topc(A_2798,'#skF_1')
      | ~ r1_tarski(A_2798,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_152882])).

tff(c_154102,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_153050,c_154064])).

tff(c_154149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_153151,c_153038,c_152807,c_154102])).

tff(c_154150,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_154374,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_154363,c_4])).

tff(c_154378,plain,(
    ! [C_3] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_3)
      | ~ r1_tarski('#skF_3',C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154374,c_2])).

tff(c_154151,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_47] :
      ( ~ r2_hidden('#skF_2',D_47)
      | ~ r1_tarski(D_47,'#skF_3')
      | ~ v3_pre_topc(D_47,'#skF_1')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_154201,plain,(
    ! [D_2811] :
      ( ~ r2_hidden('#skF_2',D_2811)
      | ~ r1_tarski(D_2811,'#skF_3')
      | ~ v3_pre_topc(D_2811,'#skF_1')
      | ~ m1_subset_1(D_2811,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154151,c_52])).

tff(c_155254,plain,(
    ! [A_2879] :
      ( ~ r2_hidden('#skF_2',A_2879)
      | ~ r1_tarski(A_2879,'#skF_3')
      | ~ v3_pre_topc(A_2879,'#skF_1')
      | ~ r1_tarski(A_2879,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_154201])).

tff(c_155290,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_154378,c_155254])).

tff(c_155329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_154652,c_154363,c_154150,c_155290])).

tff(c_155330,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_155546,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_155538,c_4])).

tff(c_155550,plain,(
    ! [C_3] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_3)
      | ~ r1_tarski('#skF_3',C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155546,c_2])).

tff(c_155331,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_47] :
      ( ~ r2_hidden('#skF_2',D_47)
      | ~ r1_tarski(D_47,'#skF_3')
      | ~ v3_pre_topc(D_47,'#skF_1')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_155730,plain,(
    ! [D_2922] :
      ( ~ r2_hidden('#skF_2',D_2922)
      | ~ r1_tarski(D_2922,'#skF_3')
      | ~ v3_pre_topc(D_2922,'#skF_1')
      | ~ m1_subset_1(D_2922,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155331,c_48])).

tff(c_156698,plain,(
    ! [A_2986] :
      ( ~ r2_hidden('#skF_2',A_2986)
      | ~ r1_tarski(A_2986,'#skF_3')
      | ~ v3_pre_topc(A_2986,'#skF_1')
      | ~ r1_tarski(A_2986,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_155730])).

tff(c_156745,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_155550,c_156698])).

tff(c_156784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_155674,c_155538,c_155330,c_156745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 57.71/46.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.71/46.54  
% 57.71/46.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.71/46.54  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 57.71/46.54  
% 57.71/46.54  %Foreground sorts:
% 57.71/46.54  
% 57.71/46.54  
% 57.71/46.54  %Background operators:
% 57.71/46.54  
% 57.71/46.54  
% 57.71/46.54  %Foreground operators:
% 57.71/46.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 57.71/46.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 57.71/46.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 57.71/46.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 57.71/46.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 57.71/46.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 57.71/46.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 57.71/46.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 57.71/46.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 57.71/46.54  tff('#skF_2', type, '#skF_2': $i).
% 57.71/46.54  tff('#skF_3', type, '#skF_3': $i).
% 57.71/46.54  tff('#skF_1', type, '#skF_1': $i).
% 57.71/46.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 57.71/46.54  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 57.71/46.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 57.71/46.54  tff('#skF_4', type, '#skF_4': $i).
% 57.71/46.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 57.71/46.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 57.71/46.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 57.71/46.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 57.71/46.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 57.71/46.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 57.71/46.54  
% 57.84/46.57  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 57.84/46.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 57.84/46.57  tff(f_87, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 57.84/46.57  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 57.84/46.57  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 57.84/46.57  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 57.84/46.57  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 57.84/46.57  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 57.84/46.57  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 57.84/46.57  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 57.84/46.57  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 57.84/46.57  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 57.84/46.57  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 57.84/46.57  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 57.84/46.57  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_65, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 57.84/46.57  tff(c_73, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_65])).
% 57.84/46.57  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_155665, plain, (![A_2915, B_2916]: (v3_pre_topc(k1_tops_1(A_2915, B_2916), A_2915) | ~m1_subset_1(B_2916, k1_zfmisc_1(u1_struct_0(A_2915))) | ~l1_pre_topc(A_2915) | ~v2_pre_topc(A_2915))), inference(cnfTransformation, [status(thm)], [f_87])).
% 57.84/46.57  tff(c_155670, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_155665])).
% 57.84/46.57  tff(c_155674, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_155670])).
% 57.84/46.57  tff(c_155529, plain, (![A_2905, B_2906]: (r1_tarski(k1_tops_1(A_2905, B_2906), B_2906) | ~m1_subset_1(B_2906, k1_zfmisc_1(u1_struct_0(A_2905))) | ~l1_pre_topc(A_2905))), inference(cnfTransformation, [status(thm)], [f_103])).
% 57.84/46.57  tff(c_155534, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_155529])).
% 57.84/46.57  tff(c_155538, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_155534])).
% 57.84/46.57  tff(c_154640, plain, (![A_2845, B_2846]: (v3_pre_topc(k1_tops_1(A_2845, B_2846), A_2845) | ~m1_subset_1(B_2846, k1_zfmisc_1(u1_struct_0(A_2845))) | ~l1_pre_topc(A_2845) | ~v2_pre_topc(A_2845))), inference(cnfTransformation, [status(thm)], [f_87])).
% 57.84/46.57  tff(c_154647, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_154640])).
% 57.84/46.57  tff(c_154652, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_154647])).
% 57.84/46.57  tff(c_154354, plain, (![A_2824, B_2825]: (r1_tarski(k1_tops_1(A_2824, B_2825), B_2825) | ~m1_subset_1(B_2825, k1_zfmisc_1(u1_struct_0(A_2824))) | ~l1_pre_topc(A_2824))), inference(cnfTransformation, [status(thm)], [f_103])).
% 57.84/46.57  tff(c_154359, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_154354])).
% 57.84/46.57  tff(c_154363, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_154359])).
% 57.84/46.57  tff(c_153142, plain, (![A_2743, B_2744]: (v3_pre_topc(k1_tops_1(A_2743, B_2744), A_2743) | ~m1_subset_1(B_2744, k1_zfmisc_1(u1_struct_0(A_2743))) | ~l1_pre_topc(A_2743) | ~v2_pre_topc(A_2743))), inference(cnfTransformation, [status(thm)], [f_87])).
% 57.84/46.57  tff(c_153147, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_153142])).
% 57.84/46.57  tff(c_153151, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_153147])).
% 57.84/46.57  tff(c_153029, plain, (![A_2735, B_2736]: (r1_tarski(k1_tops_1(A_2735, B_2736), B_2736) | ~m1_subset_1(B_2736, k1_zfmisc_1(u1_struct_0(A_2735))) | ~l1_pre_topc(A_2735))), inference(cnfTransformation, [status(thm)], [f_103])).
% 57.84/46.57  tff(c_153034, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_153029])).
% 57.84/46.57  tff(c_153038, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_153034])).
% 57.84/46.57  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 57.84/46.57  tff(c_58, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_116, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 57.84/46.57  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_107, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 57.84/46.57  tff(c_50, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_84, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 57.84/46.57  tff(c_62, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_62])).
% 57.84/46.57  tff(c_216, plain, (![A_75, B_76]: (k3_subset_1(A_75, k3_subset_1(A_75, B_76))=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 57.84/46.57  tff(c_223, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_117, c_216])).
% 57.84/46.57  tff(c_149, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k3_subset_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 57.84/46.57  tff(c_159, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_117, c_149])).
% 57.84/46.57  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 57.84/46.57  tff(c_197, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_6])).
% 57.84/46.57  tff(c_224, plain, (![B_15, A_14]: (k3_subset_1(B_15, k3_subset_1(B_15, A_14))=A_14 | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_18, c_216])).
% 57.84/46.57  tff(c_795, plain, (![A_112, B_113]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_112), B_113), A_112) | ~v3_pre_topc(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_96])).
% 57.84/46.57  tff(c_61962, plain, (![A_1390, A_1391]: (v4_pre_topc(A_1390, A_1391) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_1391), A_1390), A_1391) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_1391), A_1390), k1_zfmisc_1(u1_struct_0(A_1391))) | ~l1_pre_topc(A_1391) | ~r1_tarski(A_1390, u1_struct_0(A_1391)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_795])).
% 57.84/46.57  tff(c_61987, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_61962])).
% 57.84/46.57  tff(c_62007, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_40, c_117, c_116, c_223, c_61987])).
% 57.84/46.57  tff(c_404, plain, (![A_84, B_85]: (k2_pre_topc(A_84, B_85)=B_85 | ~v4_pre_topc(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_66])).
% 57.84/46.57  tff(c_1605, plain, (![A_158, A_159]: (k2_pre_topc(A_158, A_159)=A_159 | ~v4_pre_topc(A_159, A_158) | ~l1_pre_topc(A_158) | ~r1_tarski(A_159, u1_struct_0(A_158)))), inference(resolution, [status(thm)], [c_18, c_404])).
% 57.84/46.57  tff(c_57648, plain, (![A_1281, B_1282]: (k2_pre_topc(A_1281, k4_xboole_0(u1_struct_0(A_1281), B_1282))=k4_xboole_0(u1_struct_0(A_1281), B_1282) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(A_1281), B_1282), A_1281) | ~l1_pre_topc(A_1281))), inference(resolution, [status(thm)], [c_6, c_1605])).
% 57.84/46.57  tff(c_57674, plain, (k2_pre_topc('#skF_1', k4_xboole_0(u1_struct_0('#skF_1'), '#skF_4'))=k4_xboole_0(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_57648])).
% 57.84/46.57  tff(c_57690, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_159, c_159, c_57674])).
% 57.84/46.57  tff(c_92824, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62007, c_57690])).
% 57.84/46.57  tff(c_1135, plain, (![A_133, B_134]: (k3_subset_1(u1_struct_0(A_133), k2_pre_topc(A_133, k3_subset_1(u1_struct_0(A_133), B_134)))=k1_tops_1(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_73])).
% 57.84/46.57  tff(c_63902, plain, (![A_1440, A_1441]: (k3_subset_1(u1_struct_0(A_1440), k2_pre_topc(A_1440, A_1441))=k1_tops_1(A_1440, k3_subset_1(u1_struct_0(A_1440), A_1441)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_1440), A_1441), k1_zfmisc_1(u1_struct_0(A_1440))) | ~l1_pre_topc(A_1440) | ~r1_tarski(A_1441, u1_struct_0(A_1440)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_1135])).
% 57.84/46.57  tff(c_63927, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_63902])).
% 57.84/46.57  tff(c_63945, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')))=k1_tops_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_40, c_117, c_223, c_63927])).
% 57.84/46.57  tff(c_92825, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92824, c_63945])).
% 57.84/46.57  tff(c_92826, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_92825])).
% 57.84/46.57  tff(c_36, plain, (![A_32, B_36, C_38]: (r1_tarski(k1_tops_1(A_32, B_36), k1_tops_1(A_32, C_38)) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_115])).
% 57.84/46.57  tff(c_93167, plain, (![C_38]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_38)) | ~r1_tarski('#skF_4', C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_92826, c_36])).
% 57.84/46.57  tff(c_152407, plain, (![C_2703]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_2703)) | ~r1_tarski('#skF_4', C_2703) | ~m1_subset_1(C_2703, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_117, c_93167])).
% 57.84/46.57  tff(c_152427, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_152407])).
% 57.84/46.57  tff(c_152439, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_152427])).
% 57.84/46.57  tff(c_98, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 57.84/46.57  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 57.84/46.57  tff(c_164, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)=B_71 | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_98, c_4])).
% 57.84/46.57  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 57.84/46.57  tff(c_170, plain, (![A_70, C_3, B_71]: (r1_tarski(k1_tarski(A_70), C_3) | ~r1_tarski(B_71, C_3) | ~r2_hidden(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_164, c_2])).
% 57.84/46.57  tff(c_152668, plain, (![A_2707]: (r1_tarski(k1_tarski(A_2707), k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_2707, '#skF_4'))), inference(resolution, [status(thm)], [c_152439, c_170])).
% 57.84/46.57  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 57.84/46.57  tff(c_152721, plain, (![A_2708]: (r2_hidden(A_2708, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_2708, '#skF_4'))), inference(resolution, [status(thm)], [c_152668, c_8])).
% 57.84/46.57  tff(c_44, plain, (![D_47]: (~r2_hidden('#skF_2', D_47) | ~r1_tarski(D_47, '#skF_3') | ~v3_pre_topc(D_47, '#skF_1') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_549, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 57.84/46.57  tff(c_152741, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_152721, c_549])).
% 57.84/46.57  tff(c_152758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_152741])).
% 57.84/46.57  tff(c_152761, plain, (![D_2709]: (~r2_hidden('#skF_2', D_2709) | ~r1_tarski(D_2709, '#skF_3') | ~v3_pre_topc(D_2709, '#skF_1') | ~m1_subset_1(D_2709, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 57.84/46.57  tff(c_152768, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_117, c_152761])).
% 57.84/46.57  tff(c_152782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_107, c_84, c_152768])).
% 57.84/46.57  tff(c_152784, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 57.84/46.57  tff(c_152788, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_152784])).
% 57.84/46.57  tff(c_111, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_107, c_4])).
% 57.84/46.57  tff(c_152789, plain, (![A_2710, C_2711, B_2712]: (r1_tarski(A_2710, C_2711) | ~r1_tarski(k2_xboole_0(A_2710, B_2712), C_2711))), inference(cnfTransformation, [status(thm)], [f_29])).
% 57.84/46.57  tff(c_152799, plain, (![C_2713]: (r1_tarski('#skF_4', C_2713) | ~r1_tarski('#skF_3', C_2713))), inference(superposition, [status(thm), theory('equality')], [c_111, c_152789])).
% 57.84/46.57  tff(c_152802, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_73, c_152799])).
% 57.84/46.57  tff(c_152806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152788, c_152802])).
% 57.84/46.57  tff(c_152807, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 57.84/46.57  tff(c_153046, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_153038, c_4])).
% 57.84/46.57  tff(c_153050, plain, (![C_3]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_3) | ~r1_tarski('#skF_3', C_3))), inference(superposition, [status(thm), theory('equality')], [c_153046, c_2])).
% 57.84/46.57  tff(c_152808, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 57.84/46.57  tff(c_56, plain, (![D_47]: (~r2_hidden('#skF_2', D_47) | ~r1_tarski(D_47, '#skF_3') | ~v3_pre_topc(D_47, '#skF_1') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_152882, plain, (![D_2727]: (~r2_hidden('#skF_2', D_2727) | ~r1_tarski(D_2727, '#skF_3') | ~v3_pre_topc(D_2727, '#skF_1') | ~m1_subset_1(D_2727, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_152808, c_56])).
% 57.84/46.57  tff(c_154064, plain, (![A_2798]: (~r2_hidden('#skF_2', A_2798) | ~r1_tarski(A_2798, '#skF_3') | ~v3_pre_topc(A_2798, '#skF_1') | ~r1_tarski(A_2798, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_152882])).
% 57.84/46.57  tff(c_154102, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_153050, c_154064])).
% 57.84/46.57  tff(c_154149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_153151, c_153038, c_152807, c_154102])).
% 57.84/46.57  tff(c_154150, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 57.84/46.57  tff(c_154374, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_154363, c_4])).
% 57.84/46.57  tff(c_154378, plain, (![C_3]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_3) | ~r1_tarski('#skF_3', C_3))), inference(superposition, [status(thm), theory('equality')], [c_154374, c_2])).
% 57.84/46.57  tff(c_154151, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 57.84/46.57  tff(c_52, plain, (![D_47]: (~r2_hidden('#skF_2', D_47) | ~r1_tarski(D_47, '#skF_3') | ~v3_pre_topc(D_47, '#skF_1') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_154201, plain, (![D_2811]: (~r2_hidden('#skF_2', D_2811) | ~r1_tarski(D_2811, '#skF_3') | ~v3_pre_topc(D_2811, '#skF_1') | ~m1_subset_1(D_2811, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_154151, c_52])).
% 57.84/46.57  tff(c_155254, plain, (![A_2879]: (~r2_hidden('#skF_2', A_2879) | ~r1_tarski(A_2879, '#skF_3') | ~v3_pre_topc(A_2879, '#skF_1') | ~r1_tarski(A_2879, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_154201])).
% 57.84/46.57  tff(c_155290, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_154378, c_155254])).
% 57.84/46.57  tff(c_155329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_154652, c_154363, c_154150, c_155290])).
% 57.84/46.57  tff(c_155330, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 57.84/46.57  tff(c_155546, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_155538, c_4])).
% 57.84/46.57  tff(c_155550, plain, (![C_3]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_3) | ~r1_tarski('#skF_3', C_3))), inference(superposition, [status(thm), theory('equality')], [c_155546, c_2])).
% 57.84/46.57  tff(c_155331, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 57.84/46.57  tff(c_48, plain, (![D_47]: (~r2_hidden('#skF_2', D_47) | ~r1_tarski(D_47, '#skF_3') | ~v3_pre_topc(D_47, '#skF_1') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 57.84/46.57  tff(c_155730, plain, (![D_2922]: (~r2_hidden('#skF_2', D_2922) | ~r1_tarski(D_2922, '#skF_3') | ~v3_pre_topc(D_2922, '#skF_1') | ~m1_subset_1(D_2922, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_155331, c_48])).
% 57.84/46.57  tff(c_156698, plain, (![A_2986]: (~r2_hidden('#skF_2', A_2986) | ~r1_tarski(A_2986, '#skF_3') | ~v3_pre_topc(A_2986, '#skF_1') | ~r1_tarski(A_2986, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_155730])).
% 57.84/46.57  tff(c_156745, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_155550, c_156698])).
% 57.84/46.57  tff(c_156784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_155674, c_155538, c_155330, c_156745])).
% 57.84/46.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.84/46.57  
% 57.84/46.57  Inference rules
% 57.84/46.57  ----------------------
% 57.84/46.57  #Ref     : 0
% 57.84/46.57  #Sup     : 40928
% 57.84/46.57  #Fact    : 0
% 57.84/46.57  #Define  : 0
% 57.84/46.57  #Split   : 100
% 57.84/46.57  #Chain   : 0
% 57.84/46.57  #Close   : 0
% 57.84/46.57  
% 57.84/46.57  Ordering : KBO
% 57.84/46.57  
% 57.84/46.57  Simplification rules
% 57.84/46.57  ----------------------
% 57.84/46.57  #Subsume      : 10658
% 57.84/46.57  #Demod        : 13010
% 57.84/46.57  #Tautology    : 7367
% 57.84/46.57  #SimpNegUnit  : 124
% 57.84/46.57  #BackRed      : 287
% 57.84/46.57  
% 57.84/46.57  #Partial instantiations: 0
% 57.84/46.57  #Strategies tried      : 1
% 57.84/46.57  
% 57.84/46.57  Timing (in seconds)
% 57.84/46.57  ----------------------
% 57.84/46.57  Preprocessing        : 0.35
% 57.84/46.57  Parsing              : 0.18
% 57.84/46.57  CNF conversion       : 0.03
% 57.84/46.57  Main loop            : 45.43
% 57.84/46.57  Inferencing          : 4.79
% 57.84/46.57  Reduction            : 21.07
% 57.84/46.57  Demodulation         : 17.16
% 57.84/46.57  BG Simplification    : 0.44
% 57.84/46.57  Subsumption          : 15.79
% 57.84/46.57  Abstraction          : 0.62
% 57.84/46.57  MUC search           : 0.00
% 57.84/46.57  Cooper               : 0.00
% 57.84/46.57  Total                : 45.83
% 57.84/46.57  Index Insertion      : 0.00
% 57.84/46.57  Index Deletion       : 0.00
% 57.84/46.57  Index Matching       : 0.00
% 57.84/46.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
