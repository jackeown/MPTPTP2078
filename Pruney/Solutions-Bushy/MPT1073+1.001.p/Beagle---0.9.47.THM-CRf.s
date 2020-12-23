%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1073+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 106 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_10,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15,D_16),A_13)
      | ~ r2_hidden(C_15,k2_relset_1(A_13,B_14,D_16))
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(D_16,A_13,B_14)
      | ~ v1_funct_1(D_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',C_15,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_15,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_29,plain,(
    ! [C_17] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',C_17,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_17,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_25])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [C_18] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4',C_18,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_18,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_29,c_6])).

tff(c_38,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_8,plain,(
    ! [E_9] :
      ( k1_funct_1('#skF_5',E_9) != '#skF_2'
      | ~ m1_subset_1(E_9,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_43,plain,(
    ! [D_19,A_20,B_21,C_22] :
      ( k1_funct_1(D_19,'#skF_1'(A_20,B_21,C_22,D_19)) = C_22
      | ~ r2_hidden(C_22,k2_relset_1(A_20,B_21,D_19))
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_19,A_20,B_21)
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) = '#skF_2'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_43])).

tff(c_48,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_45])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48])).

%------------------------------------------------------------------------------
