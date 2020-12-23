%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1124+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 182 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 419 expanded)
%              Number of equality atoms :    7 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_98,plain,(
    ! [B_77,A_78] :
      ( l1_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_108,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_34,plain,(
    ! [A_43] :
      ( l1_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [A_73] :
      ( u1_struct_0(A_73) = k2_struct_0(A_73)
      | ~ l1_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_78,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_112,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_78])).

tff(c_135,plain,(
    ! [A_84] :
      ( m1_subset_1(k2_struct_0(A_84),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_150,plain,(
    ! [A_87] :
      ( r1_tarski(k2_struct_0(A_87),u1_struct_0(A_87))
      | ~ l1_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_135,c_54])).

tff(c_153,plain,
    ( r1_tarski(k2_struct_0('#skF_8'),k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_150])).

tff(c_160,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_163])).

tff(c_169,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_113,plain,(
    m1_subset_1('#skF_9',k2_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_62])).

tff(c_22,plain,(
    ! [B_24,A_2] :
      ( r1_tarski(k2_struct_0(B_24),k2_struct_0(A_2))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(A_59,B_60)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(A_61,k1_zfmisc_1(B_62))
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_286,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_426,plain,(
    ! [A_107,B_108,A_109] :
      ( m1_subset_1(A_107,B_108)
      | ~ r2_hidden(A_107,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(resolution,[status(thm)],[c_56,c_286])).

tff(c_719,plain,(
    ! [A_139,B_140,B_141] :
      ( m1_subset_1(A_139,B_140)
      | ~ r1_tarski(B_141,B_140)
      | v1_xboole_0(B_141)
      | ~ m1_subset_1(A_139,B_141) ) ),
    inference(resolution,[status(thm)],[c_52,c_426])).

tff(c_2265,plain,(
    ! [A_262,A_263,B_264] :
      ( m1_subset_1(A_262,k2_struct_0(A_263))
      | v1_xboole_0(k2_struct_0(B_264))
      | ~ m1_subset_1(A_262,k2_struct_0(B_264))
      | ~ m1_pre_topc(B_264,A_263)
      | ~ l1_pre_topc(B_264)
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_22,c_719])).

tff(c_2270,plain,(
    ! [A_263] :
      ( m1_subset_1('#skF_9',k2_struct_0(A_263))
      | v1_xboole_0(k2_struct_0('#skF_8'))
      | ~ m1_pre_topc('#skF_8',A_263)
      | ~ l1_pre_topc('#skF_8')
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_113,c_2265])).

tff(c_2277,plain,(
    ! [A_263] :
      ( m1_subset_1('#skF_9',k2_struct_0(A_263))
      | v1_xboole_0(k2_struct_0('#skF_8'))
      | ~ m1_pre_topc('#skF_8',A_263)
      | ~ l1_pre_topc(A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2270])).

tff(c_2279,plain,(
    v1_xboole_0(k2_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2277])).

tff(c_46,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(k2_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2282,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2279,c_46])).

tff(c_2285,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2282])).

tff(c_2287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2285])).

tff(c_2290,plain,(
    ! [A_265] :
      ( m1_subset_1('#skF_9',k2_struct_0(A_265))
      | ~ m1_pre_topc('#skF_8',A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(splitRight,[status(thm)],[c_2277])).

tff(c_79,plain,(
    ! [A_74] :
      ( u1_struct_0(A_74) = k2_struct_0(A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_87,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_79])).

tff(c_60,plain,(
    ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_92,plain,(
    ~ m1_subset_1('#skF_9',k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_60])).

tff(c_2295,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_2290,c_92])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2295])).

%------------------------------------------------------------------------------
