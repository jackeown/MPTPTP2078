%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 133 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 259 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1931,plain,(
    ! [B_279,A_280] :
      ( r1_tarski(B_279,k2_pre_topc(A_280,B_279))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1933,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1931])).

tff(c_1936,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1933])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = A_39
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_2144,plain,(
    ! [A_335,B_336] :
      ( m1_subset_1(k2_pre_topc(A_335,B_336),k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2733,plain,(
    ! [A_457,B_458,C_459] :
      ( k7_subset_1(u1_struct_0(A_457),k2_pre_topc(A_457,B_458),C_459) = k4_xboole_0(k2_pre_topc(A_457,B_458),C_459)
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457) ) ),
    inference(resolution,[status(thm)],[c_2144,c_16])).

tff(c_2737,plain,(
    ! [C_459] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_459) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_459)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_2733])).

tff(c_2742,plain,(
    ! [C_460] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_460) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_460) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2737])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_90,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_388,plain,(
    ! [B_86,A_87] :
      ( v2_tops_1(B_86,A_87)
      | k1_tops_1(A_87,B_86) != k1_xboole_0
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_391,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_388])).

tff(c_394,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_391])).

tff(c_395,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_394])).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_142,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_42])).

tff(c_450,plain,(
    ! [A_96,B_97] :
      ( r1_xboole_0(k1_tops_1(A_96,B_97),k2_tops_1(A_96,B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1464,plain,(
    ! [A_240,B_241] :
      ( k4_xboole_0(k1_tops_1(A_240,B_241),k2_tops_1(A_240,B_241)) = k1_tops_1(A_240,B_241)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_450,c_10])).

tff(c_1468,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1464])).

tff(c_1472,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1468])).

tff(c_298,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_tops_1(A_73,B_74),B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_300,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_298])).

tff(c_303,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_300])).

tff(c_143,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_xboole_0(A_45,k4_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_196,plain,(
    ! [C_60,B_61,A_62] :
      ( r1_xboole_0(k4_xboole_0(C_60,B_61),A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_311,plain,(
    ! [C_79,B_80,A_81] :
      ( k4_xboole_0(k4_xboole_0(C_79,B_80),A_81) = k4_xboole_0(C_79,B_80)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_196,c_10])).

tff(c_160,plain,(
    ! [C_46,B_47,A_45] :
      ( r1_xboole_0(k4_xboole_0(C_46,B_47),A_45)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_396,plain,(
    ! [C_88,B_89,A_90,A_91] :
      ( r1_xboole_0(k4_xboole_0(C_88,B_89),A_90)
      | ~ r1_tarski(A_90,A_91)
      | ~ r1_tarski(A_91,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_160])).

tff(c_403,plain,(
    ! [C_88,B_89] :
      ( r1_xboole_0(k4_xboole_0(C_88,B_89),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_89) ) ),
    inference(resolution,[status(thm)],[c_303,c_396])).

tff(c_1544,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1472,c_403])).

tff(c_1593,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1544])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ r1_xboole_0(A_4,A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1606,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1593,c_8])).

tff(c_1613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_1606])).

tff(c_1615,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2062,plain,(
    ! [A_307,B_308] :
      ( k1_tops_1(A_307,B_308) = k1_xboole_0
      | ~ v2_tops_1(B_308,A_307)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2065,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2062])).

tff(c_2068,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1615,c_2065])).

tff(c_2162,plain,(
    ! [A_337,B_338] :
      ( k7_subset_1(u1_struct_0(A_337),k2_pre_topc(A_337,B_338),k1_tops_1(A_337,B_338)) = k2_tops_1(A_337,B_338)
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2171,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2068,c_2162])).

tff(c_2175,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2171])).

tff(c_2748,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2742,c_2175])).

tff(c_2764,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2748])).

tff(c_1614,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1616,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1614,c_1616])).

tff(c_1657,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2772,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2764,c_1657])).

tff(c_2775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_2772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.02  
% 5.13/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.02  %$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.13/2.02  
% 5.13/2.02  %Foreground sorts:
% 5.13/2.02  
% 5.13/2.02  
% 5.13/2.02  %Background operators:
% 5.13/2.02  
% 5.13/2.02  
% 5.13/2.02  %Foreground operators:
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/2.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.13/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/2.02  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.13/2.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.13/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/2.02  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.13/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.13/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.13/2.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.13/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.13/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/2.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.13/2.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.13/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/2.02  
% 5.13/2.04  tff(f_108, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 5.13/2.04  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 5.13/2.04  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.13/2.04  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.13/2.04  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.13/2.04  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.13/2.04  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.13/2.04  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 5.13/2.04  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.13/2.04  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.13/2.04  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.13/2.04  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.13/2.04  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.13/2.04  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.13/2.04  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.13/2.04  tff(c_1931, plain, (![B_279, A_280]: (r1_tarski(B_279, k2_pre_topc(A_280, B_279)) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.13/2.04  tff(c_1933, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1931])).
% 5.13/2.04  tff(c_1936, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1933])).
% 5.13/2.04  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.13/2.04  tff(c_77, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=A_39 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.13/2.04  tff(c_89, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(resolution, [status(thm)], [c_4, c_77])).
% 5.13/2.04  tff(c_2144, plain, (![A_335, B_336]: (m1_subset_1(k2_pre_topc(A_335, B_336), k1_zfmisc_1(u1_struct_0(A_335))) | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.13/2.04  tff(c_16, plain, (![A_10, B_11, C_12]: (k7_subset_1(A_10, B_11, C_12)=k4_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.13/2.04  tff(c_2733, plain, (![A_457, B_458, C_459]: (k7_subset_1(u1_struct_0(A_457), k2_pre_topc(A_457, B_458), C_459)=k4_xboole_0(k2_pre_topc(A_457, B_458), C_459) | ~m1_subset_1(B_458, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457))), inference(resolution, [status(thm)], [c_2144, c_16])).
% 5.13/2.04  tff(c_2737, plain, (![C_459]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_459)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_459) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_2733])).
% 5.13/2.04  tff(c_2742, plain, (![C_460]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_460)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_460))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2737])).
% 5.13/2.04  tff(c_36, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.13/2.04  tff(c_90, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 5.13/2.04  tff(c_388, plain, (![B_86, A_87]: (v2_tops_1(B_86, A_87) | k1_tops_1(A_87, B_86)!=k1_xboole_0 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/2.04  tff(c_391, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_388])).
% 5.13/2.04  tff(c_394, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_391])).
% 5.13/2.04  tff(c_395, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_394])).
% 5.13/2.04  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.13/2.04  tff(c_142, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_90, c_42])).
% 5.13/2.04  tff(c_450, plain, (![A_96, B_97]: (r1_xboole_0(k1_tops_1(A_96, B_97), k2_tops_1(A_96, B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.13/2.04  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.13/2.04  tff(c_1464, plain, (![A_240, B_241]: (k4_xboole_0(k1_tops_1(A_240, B_241), k2_tops_1(A_240, B_241))=k1_tops_1(A_240, B_241) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_450, c_10])).
% 5.13/2.04  tff(c_1468, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1464])).
% 5.13/2.04  tff(c_1472, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1468])).
% 5.13/2.04  tff(c_298, plain, (![A_73, B_74]: (r1_tarski(k1_tops_1(A_73, B_74), B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.13/2.04  tff(c_300, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_298])).
% 5.13/2.04  tff(c_303, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_300])).
% 5.13/2.04  tff(c_143, plain, (![A_45, C_46, B_47]: (r1_xboole_0(A_45, k4_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/2.04  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.13/2.04  tff(c_196, plain, (![C_60, B_61, A_62]: (r1_xboole_0(k4_xboole_0(C_60, B_61), A_62) | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_143, c_2])).
% 5.13/2.04  tff(c_311, plain, (![C_79, B_80, A_81]: (k4_xboole_0(k4_xboole_0(C_79, B_80), A_81)=k4_xboole_0(C_79, B_80) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_196, c_10])).
% 5.13/2.04  tff(c_160, plain, (![C_46, B_47, A_45]: (r1_xboole_0(k4_xboole_0(C_46, B_47), A_45) | ~r1_tarski(A_45, B_47))), inference(resolution, [status(thm)], [c_143, c_2])).
% 5.13/2.04  tff(c_396, plain, (![C_88, B_89, A_90, A_91]: (r1_xboole_0(k4_xboole_0(C_88, B_89), A_90) | ~r1_tarski(A_90, A_91) | ~r1_tarski(A_91, B_89))), inference(superposition, [status(thm), theory('equality')], [c_311, c_160])).
% 5.13/2.04  tff(c_403, plain, (![C_88, B_89]: (r1_xboole_0(k4_xboole_0(C_88, B_89), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_89))), inference(resolution, [status(thm)], [c_303, c_396])).
% 5.13/2.04  tff(c_1544, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1472, c_403])).
% 5.13/2.04  tff(c_1593, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1544])).
% 5.13/2.04  tff(c_8, plain, (![A_4]: (~r1_xboole_0(A_4, A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.13/2.04  tff(c_1606, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1593, c_8])).
% 5.13/2.04  tff(c_1613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_1606])).
% 5.13/2.04  tff(c_1615, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 5.13/2.04  tff(c_2062, plain, (![A_307, B_308]: (k1_tops_1(A_307, B_308)=k1_xboole_0 | ~v2_tops_1(B_308, A_307) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/2.04  tff(c_2065, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2062])).
% 5.13/2.04  tff(c_2068, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1615, c_2065])).
% 5.13/2.04  tff(c_2162, plain, (![A_337, B_338]: (k7_subset_1(u1_struct_0(A_337), k2_pre_topc(A_337, B_338), k1_tops_1(A_337, B_338))=k2_tops_1(A_337, B_338) | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.13/2.04  tff(c_2171, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2068, c_2162])).
% 5.13/2.04  tff(c_2175, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2171])).
% 5.13/2.04  tff(c_2748, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2742, c_2175])).
% 5.13/2.04  tff(c_2764, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2748])).
% 5.13/2.04  tff(c_1614, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 5.13/2.04  tff(c_1616, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 5.13/2.04  tff(c_1655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1614, c_1616])).
% 5.13/2.04  tff(c_1657, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 5.13/2.04  tff(c_2772, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2764, c_1657])).
% 5.13/2.04  tff(c_2775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1936, c_2772])).
% 5.13/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.04  
% 5.13/2.04  Inference rules
% 5.13/2.04  ----------------------
% 5.13/2.04  #Ref     : 0
% 5.13/2.04  #Sup     : 782
% 5.13/2.04  #Fact    : 0
% 5.13/2.04  #Define  : 0
% 5.13/2.04  #Split   : 18
% 5.13/2.04  #Chain   : 0
% 5.13/2.04  #Close   : 0
% 5.13/2.04  
% 5.13/2.04  Ordering : KBO
% 5.13/2.04  
% 5.13/2.04  Simplification rules
% 5.13/2.04  ----------------------
% 5.13/2.04  #Subsume      : 193
% 5.13/2.04  #Demod        : 173
% 5.13/2.04  #Tautology    : 143
% 5.13/2.04  #SimpNegUnit  : 6
% 5.13/2.04  #BackRed      : 5
% 5.13/2.04  
% 5.13/2.04  #Partial instantiations: 0
% 5.13/2.04  #Strategies tried      : 1
% 5.13/2.04  
% 5.13/2.04  Timing (in seconds)
% 5.13/2.04  ----------------------
% 5.13/2.05  Preprocessing        : 0.34
% 5.13/2.05  Parsing              : 0.19
% 5.13/2.05  CNF conversion       : 0.02
% 5.13/2.05  Main loop            : 0.85
% 5.13/2.05  Inferencing          : 0.28
% 5.13/2.05  Reduction            : 0.24
% 5.13/2.05  Demodulation         : 0.16
% 5.13/2.05  BG Simplification    : 0.03
% 5.13/2.05  Subsumption          : 0.23
% 5.13/2.05  Abstraction          : 0.04
% 5.13/2.05  MUC search           : 0.00
% 5.13/2.05  Cooper               : 0.00
% 5.13/2.05  Total                : 1.22
% 5.13/2.05  Index Insertion      : 0.00
% 5.13/2.05  Index Deletion       : 0.00
% 5.13/2.05  Index Matching       : 0.00
% 5.13/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
