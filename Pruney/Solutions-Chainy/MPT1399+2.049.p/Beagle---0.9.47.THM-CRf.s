%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 361 expanded)
%              Number of leaves         :   44 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  178 (1011 expanded)
%              Number of equality atoms :   35 ( 171 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_relat_1 > k3_subset_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

tff(f_59,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v2_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_40,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    ! [A_24] :
      ( v4_pre_topc(k2_struct_0(A_24),A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_124,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_125,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_44])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_67,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_4') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65])).

tff(c_14,plain,(
    ! [C_13,A_7,B_11] :
      ( r2_hidden(C_13,k3_subset_1(A_7,B_11))
      | r2_hidden(C_13,B_11)
      | ~ m1_subset_1(C_13,A_7)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_275,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,k3_subset_1(A_77,B_78))
      | r2_hidden(C_76,B_78)
      | ~ m1_subset_1(C_76,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77))
      | A_77 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_284,plain,(
    ! [C_76,A_5] :
      ( r2_hidden(C_76,A_5)
      | r2_hidden(C_76,'#skF_4')
      | ~ m1_subset_1(C_76,A_5)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_5))
      | A_5 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_275])).

tff(c_305,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(C_79,A_80)
      | r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_284])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_340,plain,(
    ! [C_79,A_80] :
      ( ~ r1_tarski('#skF_4',C_79)
      | r2_hidden(C_79,A_80)
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_305,c_24])).

tff(c_352,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(C_79,A_80)
      | ~ m1_subset_1(C_79,A_80)
      | A_80 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_340])).

tff(c_32,plain,(
    ! [A_25] :
      ( v3_pre_topc(k2_struct_0(A_25),A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_58,plain,(
    ! [D_40] :
      ( v3_pre_topc(D_40,'#skF_2')
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_131,plain,(
    ! [D_54] :
      ( v3_pre_topc(D_54,'#skF_2')
      | ~ r2_hidden(D_54,'#skF_4')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_58])).

tff(c_140,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_131])).

tff(c_155,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_52,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_4')
      | ~ r2_hidden('#skF_3',D_40)
      | ~ v4_pre_topc(D_40,'#skF_2')
      | ~ v3_pre_topc(D_40,'#skF_2')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_399,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,'#skF_4')
      | ~ r2_hidden('#skF_3',D_85)
      | ~ v4_pre_topc(D_85,'#skF_2')
      | ~ v3_pre_topc(D_85,'#skF_2')
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_52])).

tff(c_406,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_399])).

tff(c_416,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_406])).

tff(c_484,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_487,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_484])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_487])).

tff(c_492,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_500,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_509,plain,
    ( ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_352,c_500])).

tff(c_512,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_509])).

tff(c_38,plain,(
    ! [A_28] :
      ( ~ v2_tops_1(k2_struct_0(A_28),A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_530,plain,
    ( ~ v2_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_38])).

tff(c_540,plain,
    ( ~ v2_tops_1('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_530])).

tff(c_541,plain,(
    ~ v2_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_540])).

tff(c_18,plain,(
    ! [A_17] : k9_relat_1(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [A_17] : k9_relat_1('#skF_4',A_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_18])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_20])).

tff(c_145,plain,(
    ! [A_57] :
      ( m1_subset_1('#skF_1'(A_57),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_148,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_145])).

tff(c_150,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_148])).

tff(c_173,plain,(
    ! [A_59,B_60] :
      ( k9_relat_1(k6_relat_1(A_59),B_60) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_186,plain,(
    k9_relat_1(k6_relat_1(k2_struct_0('#skF_2')),'#skF_1'('#skF_2')) = '#skF_1'('#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_173])).

tff(c_516,plain,(
    k9_relat_1(k6_relat_1('#skF_4'),'#skF_1'('#skF_2')) = '#skF_1'('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_186])).

tff(c_526,plain,(
    '#skF_1'('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_516])).

tff(c_34,plain,(
    ! [A_26] :
      ( v2_tops_1('#skF_1'(A_26),A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_560,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_34])).

tff(c_570,plain,(
    v2_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_560])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_570])).

tff(c_587,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_606,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_587])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_606])).

tff(c_612,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_615,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_612,c_24])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.32  
% 2.75/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.32  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_relat_1 > k3_subset_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.75/1.32  
% 2.75/1.32  %Foreground sorts:
% 2.75/1.32  
% 2.75/1.32  
% 2.75/1.32  %Background operators:
% 2.75/1.32  
% 2.75/1.32  
% 2.75/1.32  %Foreground operators:
% 2.75/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.75/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.32  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.75/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.75/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.75/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.75/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.75/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.75/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.32  
% 2.75/1.34  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.75/1.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.75/1.34  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.75/1.34  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.34  tff(f_73, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.75/1.34  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.75/1.34  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.75/1.34  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.75/1.34  tff(f_35, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.75/1.34  tff(f_51, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.75/1.34  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.75/1.34  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.75/1.34  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.75/1.34  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_tops_1)).
% 2.75/1.34  tff(f_59, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.75/1.34  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.75/1.34  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v2_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 2.75/1.34  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.75/1.34  tff(c_40, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.34  tff(c_68, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2])).
% 2.75/1.34  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_30, plain, (![A_24]: (v4_pre_topc(k2_struct_0(A_24), A_24) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.34  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_28, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.34  tff(c_113, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.75/1.34  tff(c_120, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_28, c_113])).
% 2.75/1.34  tff(c_124, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_120])).
% 2.75/1.34  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_125, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_44])).
% 2.75/1.34  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.34  tff(c_62, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12])).
% 2.75/1.34  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.34  tff(c_66, plain, (![A_2]: (k1_subset_1(A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 2.75/1.34  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.34  tff(c_10, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.34  tff(c_65, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.75/1.34  tff(c_67, plain, (![A_5]: (k3_subset_1(A_5, '#skF_4')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65])).
% 2.75/1.34  tff(c_14, plain, (![C_13, A_7, B_11]: (r2_hidden(C_13, k3_subset_1(A_7, B_11)) | r2_hidden(C_13, B_11) | ~m1_subset_1(C_13, A_7) | ~m1_subset_1(B_11, k1_zfmisc_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.34  tff(c_275, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, k3_subset_1(A_77, B_78)) | r2_hidden(C_76, B_78) | ~m1_subset_1(C_76, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)) | A_77='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 2.75/1.34  tff(c_284, plain, (![C_76, A_5]: (r2_hidden(C_76, A_5) | r2_hidden(C_76, '#skF_4') | ~m1_subset_1(C_76, A_5) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_5)) | A_5='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67, c_275])).
% 2.75/1.34  tff(c_305, plain, (![C_79, A_80]: (r2_hidden(C_79, A_80) | r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, A_80) | A_80='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_284])).
% 2.75/1.34  tff(c_24, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.75/1.34  tff(c_340, plain, (![C_79, A_80]: (~r1_tarski('#skF_4', C_79) | r2_hidden(C_79, A_80) | ~m1_subset_1(C_79, A_80) | A_80='#skF_4')), inference(resolution, [status(thm)], [c_305, c_24])).
% 2.75/1.34  tff(c_352, plain, (![C_79, A_80]: (r2_hidden(C_79, A_80) | ~m1_subset_1(C_79, A_80) | A_80='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_340])).
% 2.75/1.34  tff(c_32, plain, (![A_25]: (v3_pre_topc(k2_struct_0(A_25), A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.75/1.34  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.34  tff(c_64, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.75/1.34  tff(c_58, plain, (![D_40]: (v3_pre_topc(D_40, '#skF_2') | ~r2_hidden(D_40, '#skF_4') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_131, plain, (![D_54]: (v3_pre_topc(D_54, '#skF_2') | ~r2_hidden(D_54, '#skF_4') | ~m1_subset_1(D_54, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_58])).
% 2.75/1.34  tff(c_140, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_131])).
% 2.75/1.34  tff(c_155, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_140])).
% 2.75/1.34  tff(c_52, plain, (![D_40]: (r2_hidden(D_40, '#skF_4') | ~r2_hidden('#skF_3', D_40) | ~v4_pre_topc(D_40, '#skF_2') | ~v3_pre_topc(D_40, '#skF_2') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.75/1.34  tff(c_399, plain, (![D_85]: (r2_hidden(D_85, '#skF_4') | ~r2_hidden('#skF_3', D_85) | ~v4_pre_topc(D_85, '#skF_2') | ~v3_pre_topc(D_85, '#skF_2') | ~m1_subset_1(D_85, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_52])).
% 2.75/1.34  tff(c_406, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_64, c_399])).
% 2.75/1.34  tff(c_416, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_155, c_406])).
% 2.75/1.34  tff(c_484, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_416])).
% 2.75/1.34  tff(c_487, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_484])).
% 2.75/1.34  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_487])).
% 2.75/1.34  tff(c_492, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_416])).
% 2.75/1.34  tff(c_500, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_492])).
% 2.75/1.34  tff(c_509, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_352, c_500])).
% 2.75/1.34  tff(c_512, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_509])).
% 2.75/1.34  tff(c_38, plain, (![A_28]: (~v2_tops_1(k2_struct_0(A_28), A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.75/1.34  tff(c_530, plain, (~v2_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_512, c_38])).
% 2.75/1.34  tff(c_540, plain, (~v2_tops_1('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_530])).
% 2.75/1.34  tff(c_541, plain, (~v2_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_540])).
% 2.75/1.34  tff(c_18, plain, (![A_17]: (k9_relat_1(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.34  tff(c_60, plain, (![A_17]: (k9_relat_1('#skF_4', A_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_18])).
% 2.75/1.34  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.34  tff(c_59, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_20])).
% 2.75/1.34  tff(c_145, plain, (![A_57]: (m1_subset_1('#skF_1'(A_57), k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.75/1.34  tff(c_148, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_145])).
% 2.75/1.34  tff(c_150, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_148])).
% 2.75/1.34  tff(c_173, plain, (![A_59, B_60]: (k9_relat_1(k6_relat_1(A_59), B_60)=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.34  tff(c_186, plain, (k9_relat_1(k6_relat_1(k2_struct_0('#skF_2')), '#skF_1'('#skF_2'))='#skF_1'('#skF_2')), inference(resolution, [status(thm)], [c_150, c_173])).
% 2.75/1.34  tff(c_516, plain, (k9_relat_1(k6_relat_1('#skF_4'), '#skF_1'('#skF_2'))='#skF_1'('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_186])).
% 2.75/1.34  tff(c_526, plain, ('#skF_1'('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_516])).
% 2.75/1.34  tff(c_34, plain, (![A_26]: (v2_tops_1('#skF_1'(A_26), A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.75/1.34  tff(c_560, plain, (v2_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_526, c_34])).
% 2.75/1.34  tff(c_570, plain, (v2_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_560])).
% 2.75/1.34  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_541, c_570])).
% 2.75/1.34  tff(c_587, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_492])).
% 2.75/1.34  tff(c_606, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_587])).
% 2.75/1.34  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_606])).
% 2.75/1.34  tff(c_612, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_140])).
% 2.75/1.34  tff(c_615, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_612, c_24])).
% 2.75/1.34  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_615])).
% 2.75/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.34  
% 2.75/1.34  Inference rules
% 2.75/1.34  ----------------------
% 2.75/1.34  #Ref     : 0
% 2.75/1.34  #Sup     : 103
% 2.75/1.34  #Fact    : 2
% 2.75/1.34  #Define  : 0
% 2.75/1.34  #Split   : 9
% 2.75/1.34  #Chain   : 0
% 2.75/1.34  #Close   : 0
% 2.75/1.34  
% 2.75/1.34  Ordering : KBO
% 2.75/1.34  
% 2.75/1.34  Simplification rules
% 2.75/1.34  ----------------------
% 2.75/1.34  #Subsume      : 20
% 2.75/1.34  #Demod        : 90
% 2.75/1.34  #Tautology    : 52
% 2.75/1.34  #SimpNegUnit  : 6
% 2.75/1.34  #BackRed      : 26
% 2.75/1.34  
% 2.75/1.34  #Partial instantiations: 0
% 2.75/1.34  #Strategies tried      : 1
% 2.75/1.34  
% 2.75/1.34  Timing (in seconds)
% 2.75/1.34  ----------------------
% 2.75/1.34  Preprocessing        : 0.29
% 2.75/1.34  Parsing              : 0.15
% 2.75/1.34  CNF conversion       : 0.02
% 2.75/1.34  Main loop            : 0.30
% 2.75/1.34  Inferencing          : 0.10
% 2.75/1.34  Reduction            : 0.09
% 2.75/1.34  Demodulation         : 0.07
% 2.75/1.34  BG Simplification    : 0.02
% 2.75/1.34  Subsumption          : 0.05
% 2.75/1.34  Abstraction          : 0.01
% 2.75/1.34  MUC search           : 0.00
% 2.75/1.34  Cooper               : 0.00
% 2.75/1.34  Total                : 0.63
% 2.75/1.34  Index Insertion      : 0.00
% 2.75/1.34  Index Deletion       : 0.00
% 2.75/1.34  Index Matching       : 0.00
% 2.75/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
