%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:12 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 132 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ~ ( r2_hidden(D,B)
                    <=> r2_hidden(D,C) ) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> ~ r2_hidden(D,C) ) )
           => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

tff(c_12,plain,(
    k3_subset_1('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | k3_subset_1(A_1,C_6) = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,'#skF_3')
      | r2_hidden(D_12,'#skF_4')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20),C_20)
      | ~ r2_hidden('#skF_1'(A_18,B_19,C_20),B_19)
      | k3_subset_1(A_18,C_20) = B_19
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_18,C_20] :
      ( r2_hidden('#skF_1'(A_18,'#skF_3',C_20),C_20)
      | k3_subset_1(A_18,C_20) = '#skF_3'
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_18))
      | r2_hidden('#skF_1'(A_18,'#skF_3',C_20),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_18,'#skF_3',C_20),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_32])).

tff(c_54,plain,(
    ! [A_18] :
      ( k3_subset_1(A_18,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_1'(A_18,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_18,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_36])).

tff(c_98,plain,(
    ! [A_28] :
      ( k3_subset_1(A_28,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_28))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_28))
      | ~ m1_subset_1('#skF_1'(A_28,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_28,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_36])).

tff(c_10,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | k3_subset_1(A_1,C_6) = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31,'#skF_3','#skF_4'),'#skF_3')
      | k3_subset_1(A_31,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_1'(A_31,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_98,c_10])).

tff(c_18,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_4')
      | ~ r2_hidden(D_12,'#skF_3')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_143,plain,(
    ! [A_34] :
      ( ~ r2_hidden('#skF_1'(A_34,'#skF_3','#skF_4'),'#skF_4')
      | k3_subset_1(A_34,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_1'(A_34,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_18])).

tff(c_152,plain,(
    ! [A_35] :
      ( k3_subset_1(A_35,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_1'(A_35,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_143])).

tff(c_156,plain,
    ( k3_subset_1('#skF_2','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_152])).

tff(c_159,plain,(
    k3_subset_1('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_156])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_159])).

%------------------------------------------------------------------------------
