%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1136+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 209 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [A_39] :
      ( m1_subset_1(u1_orders_2(A_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(A_39))))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_50,plain,(
    ! [A_39] :
      ( v1_relat_1(u1_orders_2(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_26,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_14] :
      ( r1_relat_2(u1_orders_2(A_14),u1_struct_0(A_14))
      | ~ v3_orders_2(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [C_41,A_42,B_43] :
      ( r2_hidden(k4_tarski(C_41,C_41),A_42)
      | ~ r2_hidden(C_41,B_43)
      | ~ r1_relat_2(A_42,B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_46,A_47,B_48] :
      ( r2_hidden(k4_tarski(A_46,A_46),A_47)
      | ~ r1_relat_2(A_47,B_48)
      | ~ v1_relat_1(A_47)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_46,B_48) ) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_102,plain,(
    ! [A_60,A_61] :
      ( r2_hidden(k4_tarski(A_60,A_60),u1_orders_2(A_61))
      | ~ v1_relat_1(u1_orders_2(A_61))
      | v1_xboole_0(u1_struct_0(A_61))
      | ~ m1_subset_1(A_60,u1_struct_0(A_61))
      | ~ v3_orders_2(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_14,plain,(
    ! [A_15,B_19,C_21] :
      ( r1_orders_2(A_15,B_19,C_21)
      | ~ r2_hidden(k4_tarski(B_19,C_21),u1_orders_2(A_15))
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [A_62,A_63] :
      ( r1_orders_2(A_62,A_63,A_63)
      | ~ v1_relat_1(u1_orders_2(A_62))
      | v1_xboole_0(u1_struct_0(A_62))
      | ~ m1_subset_1(A_63,u1_struct_0(A_62))
      | ~ v3_orders_2(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_117,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_120,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_117])).

tff(c_121,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_120])).

tff(c_122,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_125,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_22,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_135,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_22])).

tff(c_138,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_141,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_141])).

%------------------------------------------------------------------------------
