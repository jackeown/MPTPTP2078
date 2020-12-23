%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0415+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 106 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 206 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_43,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1('#skF_2'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [A_32,C_33,B_34] :
      ( m1_subset_1(A_32,C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_26,plain,(
    ! [A_20,C_22,B_21] :
      ( m1_subset_1(A_20,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    ! [A_38,A_39] :
      ( m1_subset_1(A_38,'#skF_3')
      | ~ r2_hidden(A_38,A_39)
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_125,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,'#skF_3')
      | ~ r2_hidden(B_46,'#skF_4')
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_129,plain,(
    ! [A_45,A_18] :
      ( m1_subset_1(A_45,'#skF_3')
      | v1_xboole_0(A_18)
      | ~ m1_subset_1(A_45,A_18)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_18,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_181,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_28,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_184,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_181,c_28])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_184])).

tff(c_190,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_69,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_32,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k7_setfam_1(A_42,B_43),k1_zfmisc_1(k1_zfmisc_1(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_94])).

tff(c_105,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101])).

tff(c_85,plain,(
    ! [A_40,B_41] :
      ( k7_setfam_1(A_40,k7_setfam_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_92,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87])).

tff(c_314,plain,(
    ! [A_78,D_79,B_80] :
      ( r2_hidden(k3_subset_1(A_78,D_79),B_80)
      | ~ r2_hidden(D_79,k7_setfam_1(A_78,B_80))
      | ~ m1_subset_1(D_79,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(k7_setfam_1(A_78,B_80),k1_zfmisc_1(k1_zfmisc_1(A_78)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_318,plain,(
    ! [D_79] :
      ( r2_hidden(k3_subset_1('#skF_3',D_79),k1_xboole_0)
      | ~ r2_hidden(D_79,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_79,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_314])).

tff(c_353,plain,(
    ! [D_82] :
      ( r2_hidden(k3_subset_1('#skF_3',D_82),k1_xboole_0)
      | ~ r2_hidden(D_82,'#skF_4')
      | ~ m1_subset_1(D_82,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_36,c_92,c_318])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_367,plain,(
    ! [D_82] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_82,'#skF_4')
      | ~ m1_subset_1(D_82,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_353,c_30])).

tff(c_378,plain,(
    ! [D_83] :
      ( ~ r2_hidden(D_83,'#skF_4')
      | ~ m1_subset_1(D_83,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_367])).

tff(c_407,plain,(
    ! [A_84] : ~ r2_hidden(A_84,'#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_378])).

tff(c_411,plain,(
    ! [A_18] :
      ( v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_18,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_407])).

tff(c_415,plain,(
    ! [A_85] : ~ m1_subset_1(A_85,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_411])).

tff(c_425,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_20,c_415])).

%------------------------------------------------------------------------------
