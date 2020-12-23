%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 11.42s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 200 expanded)
%              Number of leaves         :   36 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 ( 554 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_81,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_80,plain,(
    ~ m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))
    | m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_110,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_62])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_721,plain,(
    ! [B_136,A_137,C_138] :
      ( r2_hidden(B_136,k1_tops_1(A_137,C_138))
      | ~ m1_connsp_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_136,u1_struct_0(A_137))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_741,plain,(
    ! [B_136,A_137,A_14] :
      ( r2_hidden(B_136,k1_tops_1(A_137,A_14))
      | ~ m1_connsp_2(A_14,A_137,B_136)
      | ~ m1_subset_1(B_136,u1_struct_0(A_137))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ r1_tarski(A_14,u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_26,c_721])).

tff(c_28,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_167,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_168,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_30,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_171,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_30])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_171])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_177])).

tff(c_182,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_185,plain,(
    ~ m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_80])).

tff(c_183,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_191,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k6_domain_1(A_76,B_77),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_200,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_191])).

tff(c_204,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_200])).

tff(c_205,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_204])).

tff(c_105,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tarski(A_59),k1_zfmisc_1(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_105,c_24])).

tff(c_557,plain,(
    ! [C_125,A_126,B_127] :
      ( m2_connsp_2(C_125,A_126,B_127)
      | ~ r1_tarski(B_127,k1_tops_1(A_126,C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_39381,plain,(
    ! [C_12418,A_12419,A_12420] :
      ( m2_connsp_2(C_12418,A_12419,k1_tarski(A_12420))
      | ~ m1_subset_1(C_12418,k1_zfmisc_1(u1_struct_0(A_12419)))
      | ~ m1_subset_1(k1_tarski(A_12420),k1_zfmisc_1(u1_struct_0(A_12419)))
      | ~ l1_pre_topc(A_12419)
      | ~ v2_pre_topc(A_12419)
      | ~ r2_hidden(A_12420,k1_tops_1(A_12419,C_12418)) ) ),
    inference(resolution,[status(thm)],[c_109,c_557])).

tff(c_39406,plain,(
    ! [A_12420] :
      ( m2_connsp_2('#skF_6','#skF_4',k1_tarski(A_12420))
      | ~ m1_subset_1(k1_tarski(A_12420),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ r2_hidden(A_12420,k1_tops_1('#skF_4','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_46,c_39381])).

tff(c_39484,plain,(
    ! [A_12547] :
      ( m2_connsp_2('#skF_6','#skF_4',k1_tarski(A_12547))
      | ~ m1_subset_1(k1_tarski(A_12547),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_12547,k1_tops_1('#skF_4','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_39406])).

tff(c_39497,plain,
    ( m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_205,c_39484])).

tff(c_39507,plain,(
    ~ r2_hidden('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_39497])).

tff(c_39512,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_741,c_39507])).

tff(c_39518,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_52,c_50,c_48,c_110,c_39512])).

tff(c_39520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_39518])).

tff(c_39521,plain,(
    ~ m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_39573,plain,(
    ! [A_12627,B_12628] :
      ( k6_domain_1(A_12627,B_12628) = k1_tarski(B_12628)
      | ~ m1_subset_1(B_12628,A_12627)
      | v1_xboole_0(A_12627) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_39589,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_39573])).

tff(c_39611,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_39589])).

tff(c_39615,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_39611,c_30])).

tff(c_39618,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_39615])).

tff(c_39621,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_39618])).

tff(c_39625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_39621])).

tff(c_39626,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_39589])).

tff(c_39522,plain,(
    m2_connsp_2('#skF_6','#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_39628,plain,(
    m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39626,c_39522])).

tff(c_39627,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_39589])).

tff(c_39634,plain,(
    ! [A_12635,B_12636] :
      ( m1_subset_1(k6_domain_1(A_12635,B_12636),k1_zfmisc_1(A_12635))
      | ~ m1_subset_1(B_12636,A_12635)
      | v1_xboole_0(A_12635) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39643,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39626,c_39634])).

tff(c_39647,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_39643])).

tff(c_39648,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_39627,c_39647])).

tff(c_39957,plain,(
    ! [B_12682,A_12683,C_12684] :
      ( r1_tarski(B_12682,k1_tops_1(A_12683,C_12684))
      | ~ m2_connsp_2(C_12684,A_12683,B_12682)
      | ~ m1_subset_1(C_12684,k1_zfmisc_1(u1_struct_0(A_12683)))
      | ~ m1_subset_1(B_12682,k1_zfmisc_1(u1_struct_0(A_12683)))
      | ~ l1_pre_topc(A_12683)
      | ~ v2_pre_topc(A_12683) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_39970,plain,(
    ! [B_12682] :
      ( r1_tarski(B_12682,k1_tops_1('#skF_4','#skF_6'))
      | ~ m2_connsp_2('#skF_6','#skF_4',B_12682)
      | ~ m1_subset_1(B_12682,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_39957])).

tff(c_40015,plain,(
    ! [B_12690] :
      ( r1_tarski(B_12690,k1_tops_1('#skF_4','#skF_6'))
      | ~ m2_connsp_2('#skF_6','#skF_4',B_12690)
      | ~ m1_subset_1(B_12690,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_39970])).

tff(c_40018,plain,
    ( r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6'))
    | ~ m2_connsp_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_39648,c_40015])).

tff(c_40036,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tops_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39628,c_40018])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39555,plain,(
    ! [C_12622,B_12623,A_12624] :
      ( r2_hidden(C_12622,B_12623)
      | ~ r2_hidden(C_12622,A_12624)
      | ~ r1_tarski(A_12624,B_12623) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39561,plain,(
    ! [C_10,B_12623] :
      ( r2_hidden(C_10,B_12623)
      | ~ r1_tarski(k1_tarski(C_10),B_12623) ) ),
    inference(resolution,[status(thm)],[c_10,c_39555])).

tff(c_40049,plain,(
    r2_hidden('#skF_5',k1_tops_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40036,c_39561])).

tff(c_40486,plain,(
    ! [C_12716,A_12717,B_12718] :
      ( m1_connsp_2(C_12716,A_12717,B_12718)
      | ~ r2_hidden(B_12718,k1_tops_1(A_12717,C_12716))
      | ~ m1_subset_1(C_12716,k1_zfmisc_1(u1_struct_0(A_12717)))
      | ~ m1_subset_1(B_12718,u1_struct_0(A_12717))
      | ~ l1_pre_topc(A_12717)
      | ~ v2_pre_topc(A_12717)
      | v2_struct_0(A_12717) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40496,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40049,c_40486])).

tff(c_40530,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_40496])).

tff(c_40532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_39521,c_40530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.42/4.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.42/4.37  
% 11.42/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.42/4.37  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 11.42/4.37  
% 11.42/4.37  %Foreground sorts:
% 11.42/4.37  
% 11.42/4.37  
% 11.42/4.37  %Background operators:
% 11.42/4.37  
% 11.42/4.37  
% 11.42/4.37  %Foreground operators:
% 11.42/4.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.42/4.37  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 11.42/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.42/4.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.42/4.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.42/4.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.42/4.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.42/4.37  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.42/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.42/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.42/4.37  tff('#skF_5', type, '#skF_5': $i).
% 11.42/4.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.42/4.37  tff('#skF_6', type, '#skF_6': $i).
% 11.42/4.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.42/4.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.42/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.42/4.37  tff('#skF_4', type, '#skF_4': $i).
% 11.42/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.42/4.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.42/4.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.42/4.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.42/4.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.42/4.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.42/4.37  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 11.42/4.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.42/4.37  
% 11.63/4.39  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 11.63/4.39  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.63/4.39  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 11.63/4.39  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.63/4.39  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.63/4.39  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.63/4.39  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 11.63/4.39  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 11.63/4.39  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 11.63/4.39  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.63/4.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.63/4.39  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_81, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.63/4.39  tff(c_85, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_81])).
% 11.63/4.39  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_56, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m2_connsp_2('#skF_6', '#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_80, plain, (~m2_connsp_2('#skF_6', '#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_56])).
% 11.63/4.39  tff(c_62, plain, (m2_connsp_2('#skF_6', '#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')) | m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.63/4.39  tff(c_110, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_62])).
% 11.63/4.39  tff(c_26, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.63/4.39  tff(c_721, plain, (![B_136, A_137, C_138]: (r2_hidden(B_136, k1_tops_1(A_137, C_138)) | ~m1_connsp_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_136, u1_struct_0(A_137)) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.63/4.39  tff(c_741, plain, (![B_136, A_137, A_14]: (r2_hidden(B_136, k1_tops_1(A_137, A_14)) | ~m1_connsp_2(A_14, A_137, B_136) | ~m1_subset_1(B_136, u1_struct_0(A_137)) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137) | ~r1_tarski(A_14, u1_struct_0(A_137)))), inference(resolution, [status(thm)], [c_26, c_721])).
% 11.63/4.39  tff(c_28, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.63/4.39  tff(c_151, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.63/4.39  tff(c_167, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_151])).
% 11.63/4.39  tff(c_168, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_167])).
% 11.63/4.39  tff(c_30, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.63/4.39  tff(c_171, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_168, c_30])).
% 11.63/4.39  tff(c_174, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_171])).
% 11.63/4.39  tff(c_177, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_174])).
% 11.63/4.39  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_177])).
% 11.63/4.39  tff(c_182, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_167])).
% 11.63/4.39  tff(c_185, plain, (~m2_connsp_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_80])).
% 11.63/4.39  tff(c_183, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_167])).
% 11.63/4.39  tff(c_191, plain, (![A_76, B_77]: (m1_subset_1(k6_domain_1(A_76, B_77), k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.63/4.39  tff(c_200, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_191])).
% 11.63/4.39  tff(c_204, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_200])).
% 11.63/4.39  tff(c_205, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_183, c_204])).
% 11.63/4.39  tff(c_105, plain, (![A_59, B_60]: (m1_subset_1(k1_tarski(A_59), k1_zfmisc_1(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.63/4.39  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.63/4.39  tff(c_109, plain, (![A_59, B_60]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_105, c_24])).
% 11.63/4.39  tff(c_557, plain, (![C_125, A_126, B_127]: (m2_connsp_2(C_125, A_126, B_127) | ~r1_tarski(B_127, k1_tops_1(A_126, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.63/4.39  tff(c_39381, plain, (![C_12418, A_12419, A_12420]: (m2_connsp_2(C_12418, A_12419, k1_tarski(A_12420)) | ~m1_subset_1(C_12418, k1_zfmisc_1(u1_struct_0(A_12419))) | ~m1_subset_1(k1_tarski(A_12420), k1_zfmisc_1(u1_struct_0(A_12419))) | ~l1_pre_topc(A_12419) | ~v2_pre_topc(A_12419) | ~r2_hidden(A_12420, k1_tops_1(A_12419, C_12418)))), inference(resolution, [status(thm)], [c_109, c_557])).
% 11.63/4.39  tff(c_39406, plain, (![A_12420]: (m2_connsp_2('#skF_6', '#skF_4', k1_tarski(A_12420)) | ~m1_subset_1(k1_tarski(A_12420), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r2_hidden(A_12420, k1_tops_1('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_46, c_39381])).
% 11.63/4.39  tff(c_39484, plain, (![A_12547]: (m2_connsp_2('#skF_6', '#skF_4', k1_tarski(A_12547)) | ~m1_subset_1(k1_tarski(A_12547), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_12547, k1_tops_1('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_39406])).
% 11.63/4.39  tff(c_39497, plain, (m2_connsp_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~r2_hidden('#skF_5', k1_tops_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_205, c_39484])).
% 11.63/4.39  tff(c_39507, plain, (~r2_hidden('#skF_5', k1_tops_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_185, c_39497])).
% 11.63/4.39  tff(c_39512, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_741, c_39507])).
% 11.63/4.39  tff(c_39518, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_52, c_50, c_48, c_110, c_39512])).
% 11.63/4.39  tff(c_39520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_39518])).
% 11.63/4.39  tff(c_39521, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 11.63/4.39  tff(c_39573, plain, (![A_12627, B_12628]: (k6_domain_1(A_12627, B_12628)=k1_tarski(B_12628) | ~m1_subset_1(B_12628, A_12627) | v1_xboole_0(A_12627))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.63/4.39  tff(c_39589, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_39573])).
% 11.63/4.39  tff(c_39611, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_39589])).
% 11.63/4.39  tff(c_39615, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_39611, c_30])).
% 11.63/4.39  tff(c_39618, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_39615])).
% 11.63/4.39  tff(c_39621, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_39618])).
% 11.63/4.39  tff(c_39625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_39621])).
% 11.63/4.39  tff(c_39626, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_39589])).
% 11.63/4.39  tff(c_39522, plain, (m2_connsp_2('#skF_6', '#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 11.63/4.39  tff(c_39628, plain, (m2_connsp_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_39626, c_39522])).
% 11.63/4.39  tff(c_39627, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_39589])).
% 11.63/4.39  tff(c_39634, plain, (![A_12635, B_12636]: (m1_subset_1(k6_domain_1(A_12635, B_12636), k1_zfmisc_1(A_12635)) | ~m1_subset_1(B_12636, A_12635) | v1_xboole_0(A_12635))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.63/4.39  tff(c_39643, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39626, c_39634])).
% 11.63/4.39  tff(c_39647, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_39643])).
% 11.63/4.39  tff(c_39648, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_39627, c_39647])).
% 11.63/4.39  tff(c_39957, plain, (![B_12682, A_12683, C_12684]: (r1_tarski(B_12682, k1_tops_1(A_12683, C_12684)) | ~m2_connsp_2(C_12684, A_12683, B_12682) | ~m1_subset_1(C_12684, k1_zfmisc_1(u1_struct_0(A_12683))) | ~m1_subset_1(B_12682, k1_zfmisc_1(u1_struct_0(A_12683))) | ~l1_pre_topc(A_12683) | ~v2_pre_topc(A_12683))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.63/4.39  tff(c_39970, plain, (![B_12682]: (r1_tarski(B_12682, k1_tops_1('#skF_4', '#skF_6')) | ~m2_connsp_2('#skF_6', '#skF_4', B_12682) | ~m1_subset_1(B_12682, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_39957])).
% 11.63/4.39  tff(c_40015, plain, (![B_12690]: (r1_tarski(B_12690, k1_tops_1('#skF_4', '#skF_6')) | ~m2_connsp_2('#skF_6', '#skF_4', B_12690) | ~m1_subset_1(B_12690, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_39970])).
% 11.63/4.39  tff(c_40018, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tops_1('#skF_4', '#skF_6')) | ~m2_connsp_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_39648, c_40015])).
% 11.63/4.39  tff(c_40036, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tops_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_39628, c_40018])).
% 11.63/4.39  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.63/4.39  tff(c_39555, plain, (![C_12622, B_12623, A_12624]: (r2_hidden(C_12622, B_12623) | ~r2_hidden(C_12622, A_12624) | ~r1_tarski(A_12624, B_12623))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.63/4.39  tff(c_39561, plain, (![C_10, B_12623]: (r2_hidden(C_10, B_12623) | ~r1_tarski(k1_tarski(C_10), B_12623))), inference(resolution, [status(thm)], [c_10, c_39555])).
% 11.63/4.39  tff(c_40049, plain, (r2_hidden('#skF_5', k1_tops_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_40036, c_39561])).
% 11.63/4.39  tff(c_40486, plain, (![C_12716, A_12717, B_12718]: (m1_connsp_2(C_12716, A_12717, B_12718) | ~r2_hidden(B_12718, k1_tops_1(A_12717, C_12716)) | ~m1_subset_1(C_12716, k1_zfmisc_1(u1_struct_0(A_12717))) | ~m1_subset_1(B_12718, u1_struct_0(A_12717)) | ~l1_pre_topc(A_12717) | ~v2_pre_topc(A_12717) | v2_struct_0(A_12717))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.63/4.39  tff(c_40496, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40049, c_40486])).
% 11.63/4.39  tff(c_40530, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_40496])).
% 11.63/4.39  tff(c_40532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_39521, c_40530])).
% 11.63/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/4.39  
% 11.63/4.39  Inference rules
% 11.63/4.39  ----------------------
% 11.63/4.39  #Ref     : 0
% 11.63/4.39  #Sup     : 6258
% 11.63/4.39  #Fact    : 18
% 11.63/4.39  #Define  : 0
% 11.63/4.39  #Split   : 14
% 11.63/4.39  #Chain   : 0
% 11.63/4.39  #Close   : 0
% 11.63/4.39  
% 11.63/4.39  Ordering : KBO
% 11.63/4.39  
% 11.63/4.39  Simplification rules
% 11.63/4.39  ----------------------
% 11.63/4.39  #Subsume      : 1422
% 11.63/4.39  #Demod        : 390
% 11.63/4.39  #Tautology    : 400
% 11.63/4.39  #SimpNegUnit  : 32
% 11.63/4.39  #BackRed      : 2
% 11.63/4.39  
% 11.63/4.39  #Partial instantiations: 9816
% 11.63/4.39  #Strategies tried      : 1
% 11.63/4.39  
% 11.63/4.39  Timing (in seconds)
% 11.63/4.39  ----------------------
% 11.63/4.39  Preprocessing        : 0.54
% 11.63/4.39  Parsing              : 0.29
% 11.63/4.39  CNF conversion       : 0.04
% 11.63/4.39  Main loop            : 3.07
% 11.63/4.39  Inferencing          : 1.01
% 11.63/4.39  Reduction            : 0.72
% 11.63/4.39  Demodulation         : 0.48
% 11.63/4.39  BG Simplification    : 0.16
% 11.63/4.39  Subsumption          : 0.94
% 11.63/4.39  Abstraction          : 0.18
% 11.63/4.39  MUC search           : 0.00
% 11.63/4.39  Cooper               : 0.00
% 11.63/4.39  Total                : 3.66
% 11.63/4.39  Index Insertion      : 0.00
% 11.63/4.39  Index Deletion       : 0.00
% 11.63/4.39  Index Matching       : 0.00
% 11.63/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
