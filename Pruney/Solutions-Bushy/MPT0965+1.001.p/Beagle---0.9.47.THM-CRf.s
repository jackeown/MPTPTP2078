%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0965+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:08 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 123 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_12])).

tff(c_29,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [D_32,C_33,A_34,B_35] :
      ( r2_hidden(k1_funct_1(D_32,C_33),k2_relset_1(A_34,B_35,D_32))
      | k1_xboole_0 = B_35
      | ~ r2_hidden(C_33,A_34)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(D_32,A_34,B_35)
      | ~ v1_funct_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_subset_1(k2_relset_1(A_21,B_22,C_23),k1_zfmisc_1(B_22))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [A_6,B_22,A_21,C_23] :
      ( m1_subset_1(A_6,B_22)
      | ~ r2_hidden(A_6,k2_relset_1(A_21,B_22,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(resolution,[status(thm)],[c_35,c_6])).

tff(c_111,plain,(
    ! [D_39,C_40,B_41,A_42] :
      ( m1_subset_1(k1_funct_1(D_39,C_40),B_41)
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_40,A_42)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41)))
      | ~ v1_funct_2(D_39,A_42,B_41)
      | ~ v1_funct_1(D_39) ) ),
    inference(resolution,[status(thm)],[c_52,c_38])).

tff(c_122,plain,(
    ! [D_44,B_45] :
      ( m1_subset_1(k1_funct_1(D_44,'#skF_3'),B_45)
      | k1_xboole_0 = B_45
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_45)))
      | ~ v1_funct_2(D_44,'#skF_1',B_45)
      | ~ v1_funct_1(D_44) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_129,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_133,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_129])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_29,c_133])).

tff(c_136,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_8,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_140])).

%------------------------------------------------------------------------------
