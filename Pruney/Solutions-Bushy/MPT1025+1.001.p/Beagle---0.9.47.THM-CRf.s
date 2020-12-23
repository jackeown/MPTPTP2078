%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:16 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 172 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
            & ! [F] :
                ~ ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_12,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25,plain,(
    ! [B_22,A_24,C_23,E_21,D_20] :
      ( r2_hidden('#skF_1'(D_20,E_21,B_22,C_23,A_24),A_24)
      | ~ r2_hidden(E_21,k7_relset_1(A_24,B_22,D_20,C_23))
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_24,B_22)))
      | ~ v1_funct_2(D_20,A_24,B_22)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27,plain,(
    ! [E_21,C_23] :
      ( r2_hidden('#skF_1'('#skF_5',E_21,'#skF_3',C_23,'#skF_2'),'#skF_2')
      | ~ r2_hidden(E_21,k7_relset_1('#skF_2','#skF_3','#skF_5',C_23))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_31,plain,(
    ! [E_25,C_26] :
      ( r2_hidden('#skF_1'('#skF_5',E_25,'#skF_3',C_26,'#skF_2'),'#skF_2')
      | ~ r2_hidden(E_25,k7_relset_1('#skF_2','#skF_3','#skF_5',C_26)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_27])).

tff(c_8,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [E_27,C_28] :
      ( m1_subset_1('#skF_1'('#skF_5',E_27,'#skF_3',C_28,'#skF_2'),'#skF_2')
      | ~ r2_hidden(E_27,k7_relset_1('#skF_2','#skF_3','#skF_5',C_28)) ) ),
    inference(resolution,[status(thm)],[c_31,c_8])).

tff(c_40,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_3','#skF_4','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_70,plain,(
    ! [A_42,D_38,E_39,C_41,B_40] :
      ( k1_funct_1(D_38,'#skF_1'(D_38,E_39,B_40,C_41,A_42)) = E_39
      | ~ r2_hidden(E_39,k7_relset_1(A_42,B_40,D_38,C_41))
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_42,B_40)))
      | ~ v1_funct_2(D_38,A_42,B_40)
      | ~ v1_funct_1(D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_6','#skF_3','#skF_4','#skF_2')) = '#skF_6'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_79,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_6','#skF_3','#skF_4','#skF_2')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_75])).

tff(c_41,plain,(
    ! [D_29,C_32,E_30,A_33,B_31] :
      ( r2_hidden('#skF_1'(D_29,E_30,B_31,C_32,A_33),C_32)
      | ~ r2_hidden(E_30,k7_relset_1(A_33,B_31,D_29,C_32))
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_33,B_31)))
      | ~ v1_funct_2(D_29,A_33,B_31)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [E_30,C_32] :
      ( r2_hidden('#skF_1'('#skF_5',E_30,'#skF_3',C_32,'#skF_2'),C_32)
      | ~ r2_hidden(E_30,k7_relset_1('#skF_2','#skF_3','#skF_5',C_32))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_47,plain,(
    ! [E_34,C_35] :
      ( r2_hidden('#skF_1'('#skF_5',E_34,'#skF_3',C_35,'#skF_2'),C_35)
      | ~ r2_hidden(E_34,k7_relset_1('#skF_2','#skF_3','#skF_5',C_35)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_43])).

tff(c_10,plain,(
    ! [F_16] :
      ( k1_funct_1('#skF_5',F_16) != '#skF_6'
      | ~ r2_hidden(F_16,'#skF_4')
      | ~ m1_subset_1(F_16,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    ! [E_43] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5',E_43,'#skF_3','#skF_4','#skF_2')) != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5',E_43,'#skF_3','#skF_4','#skF_2'),'#skF_2')
      | ~ r2_hidden(E_43,k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_47,c_10])).

tff(c_91,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_5','#skF_6','#skF_3','#skF_4','#skF_2')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_3','#skF_4','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_79,c_91])).

%------------------------------------------------------------------------------
