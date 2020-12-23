%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:17 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 128 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 598 expanded)
%              Number of equality atoms :    9 (  43 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r1_partfun1(C,D)
           => ( ( B = k1_xboole_0
                & A != k1_xboole_0 )
              | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(c_6,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [B_10,A_11,C_12,D_13] :
      ( k1_xboole_0 = B_10
      | r2_relset_1(A_11,B_10,C_12,D_13)
      | ~ r1_partfun1(C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_10)))
      | ~ v1_funct_2(D_13,A_11,B_10)
      | ~ v1_funct_1(D_13)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_11,B_10)))
      | ~ v1_funct_2(C_12,A_11,B_10)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_2')
      | ~ r1_partfun1(C_12,'#skF_2')
      | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_29,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_2')
      | ~ r1_partfun1(C_12,'#skF_2')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24])).

tff(c_33,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_2,plain,(
    ! [B_2,C_3,D_5] :
      ( r2_relset_1(k1_xboole_0,B_2,C_3,D_5)
      | ~ r1_partfun1(C_3,D_5)
      | ~ m1_subset_1(D_5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(D_5,k1_xboole_0,B_2)
      | ~ v1_funct_1(D_5)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [B_14,C_15,D_16] :
      ( r2_relset_1('#skF_1',B_14,C_15,D_16)
      | ~ r1_partfun1(C_15,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_14)))
      | ~ v1_funct_2(D_16,'#skF_1',B_14)
      | ~ v1_funct_1(D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_14)))
      | ~ v1_funct_2(C_15,'#skF_1',B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_33,c_33,c_33,c_33,c_2])).

tff(c_45,plain,(
    ! [C_15] :
      ( r2_relset_1('#skF_1','#skF_1',C_15,'#skF_3')
      | ~ r1_partfun1(C_15,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_15,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_79,plain,(
    ! [C_22] :
      ( r2_relset_1('#skF_1','#skF_1',C_22,'#skF_3')
      | ~ r1_partfun1(C_22,'#skF_3')
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_22,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_45])).

tff(c_82,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_88,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_8,c_82])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_88])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_26,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_3')
      | ~ r1_partfun1(C_12,'#skF_3')
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_32,plain,(
    ! [C_12] :
      ( k1_xboole_0 = '#skF_1'
      | r2_relset_1('#skF_1','#skF_1',C_12,'#skF_3')
      | ~ r1_partfun1(C_12,'#skF_3')
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_12,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_26])).

tff(c_109,plain,(
    ! [C_24] :
      ( r2_relset_1('#skF_1','#skF_1',C_24,'#skF_3')
      | ~ r1_partfun1(C_24,'#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_funct_2(C_24,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_32])).

tff(c_112,plain,
    ( r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3')
    | ~ r1_partfun1('#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_118,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_8,c_112])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_118])).

%------------------------------------------------------------------------------
