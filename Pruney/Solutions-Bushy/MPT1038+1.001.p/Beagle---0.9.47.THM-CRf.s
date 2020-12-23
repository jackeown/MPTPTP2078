%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1038+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:18 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 191 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 624 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
               => ( ( r1_partfun1(B,D)
                    & r1_partfun1(C,D) )
                 => r1_partfun1(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ( ( r1_partfun1(C,E)
                  & r1_partfun1(D,E)
                  & v1_partfun1(E,A) )
               => r1_partfun1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_16,plain,(
    ~ r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    r1_partfun1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_49,plain,(
    ! [C_34,B_35,A_36] :
      ( v1_xboole_0(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(B_35,A_36)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_80,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_partfun1(C_39,A_40)
      | ~ v1_funct_2(C_39,A_40,B_41)
      | ~ v1_funct_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | v1_xboole_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_100,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_89])).

tff(c_101,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_100])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_102,plain,(
    ! [A_46,E_43,D_42,C_44,B_45] :
      ( r1_partfun1(C_44,D_42)
      | ~ v1_partfun1(E_43,A_46)
      | ~ r1_partfun1(D_42,E_43)
      | ~ r1_partfun1(C_44,E_43)
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1(E_43)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1(D_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_106,plain,(
    ! [C_44,A_46,B_45] :
      ( r1_partfun1(C_44,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_46)
      | ~ r1_partfun1(C_44,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45)))
      | ~ v1_funct_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_118,plain,(
    ! [C_47,A_48,B_49] :
      ( r1_partfun1(C_47,'#skF_3')
      | ~ v1_partfun1('#skF_4',A_48)
      | ~ r1_partfun1(C_47,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_106])).

tff(c_120,plain,(
    ! [C_47] :
      ( r1_partfun1(C_47,'#skF_3')
      | ~ v1_partfun1('#skF_4','#skF_1')
      | ~ r1_partfun1(C_47,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_124,plain,(
    ! [C_50] :
      ( r1_partfun1(C_50,'#skF_3')
      | ~ r1_partfun1(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_101,c_120])).

tff(c_127,plain,
    ( r1_partfun1('#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_124])).

tff(c_136,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20,c_127])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_136])).

tff(c_140,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_61,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_169,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_61])).

tff(c_14,plain,(
    ! [B_24,A_23] :
      ( ~ v1_xboole_0(B_24)
      | B_24 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_173,plain,(
    ! [A_52] :
      ( A_52 = '#skF_1'
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_186,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_173])).

tff(c_60,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_148,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_60])).

tff(c_187,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_148,c_173])).

tff(c_215,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_187])).

tff(c_139,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_190,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_139,c_173])).

tff(c_202,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_190])).

tff(c_205,plain,(
    ~ r1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_16])).

tff(c_227,plain,(
    ~ r1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_205])).

tff(c_206,plain,(
    r1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_20])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_206])).

%------------------------------------------------------------------------------
