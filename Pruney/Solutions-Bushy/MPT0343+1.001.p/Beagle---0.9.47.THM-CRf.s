%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0343+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:08 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 161 expanded)
%              Number of leaves         :   14 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 560 expanded)
%              Number of equality atoms :    6 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_3,B_4,C_8] :
      ( m1_subset_1('#skF_1'(A_3,B_4,C_8),A_3)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_3,B_4,C_8] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_8),B_4)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_3')
      | ~ r2_hidden(D_14,'#skF_4')
      | ~ m1_subset_1(D_14,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r2_hidden('#skF_1'(A_23,B_24,C_25),C_25)
      | r1_tarski(B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    ! [B_26,A_27] :
      ( r1_tarski(B_26,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ r2_hidden('#skF_1'(A_27,B_26,'#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_27,B_26,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_61,plain,(
    ! [A_3] :
      ( ~ m1_subset_1('#skF_1'(A_3,'#skF_4','#skF_3'),'#skF_2')
      | r1_tarski('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_64,plain,(
    ! [A_31] :
      ( ~ m1_subset_1('#skF_1'(A_31,'#skF_4','#skF_3'),'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_31)) ) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_68,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_71,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_73,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_73])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden('#skF_1'(A_20,B_21,C_22),B_21)
      | r1_tarski(B_21,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_4')
      | ~ r2_hidden(D_14,'#skF_3')
      | ~ m1_subset_1(D_14,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_32,C_33] :
      ( r2_hidden('#skF_1'(A_32,'#skF_3',C_33),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_32,'#skF_3',C_33),'#skF_2')
      | r1_tarski('#skF_3',C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_32))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_38,c_22])).

tff(c_8,plain,(
    ! [A_3,B_4,C_8] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_8),C_8)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_32] :
      ( ~ m1_subset_1('#skF_1'(A_32,'#skF_3','#skF_4'),'#skF_2')
      | r1_tarski('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_32))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_91,plain,(
    ! [A_34] :
      ( ~ m1_subset_1('#skF_1'(A_34,'#skF_3','#skF_4'),'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_34)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_85])).

tff(c_95,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_98,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_98])).

tff(c_101,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_103,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_103])).

tff(c_107,plain,(
    ! [A_35,C_36] :
      ( r2_hidden('#skF_1'(A_35,'#skF_3',C_36),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_35,'#skF_3',C_36),'#skF_2')
      | r1_tarski('#skF_3',C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_38,c_22])).

tff(c_115,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_1'(A_35,'#skF_3','#skF_4'),'#skF_2')
      | r1_tarski('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_121,plain,(
    ! [A_37] :
      ( ~ m1_subset_1('#skF_1'(A_37,'#skF_3','#skF_4'),'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_106,c_115])).

tff(c_125,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_128,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_125])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_128])).

%------------------------------------------------------------------------------
