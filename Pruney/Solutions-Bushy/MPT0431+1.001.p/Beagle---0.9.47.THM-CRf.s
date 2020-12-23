%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0431+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:18 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 143 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_36,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ v3_setfam_1(B_31,A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64])).

tff(c_32,plain,(
    v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_67])).

tff(c_85,plain,(
    ! [A_35,B_36,C_37] :
      ( k4_subset_1(A_35,B_36,C_37) = k2_xboole_0(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_205,plain,(
    ! [B_45] :
      ( k4_subset_1(k1_zfmisc_1('#skF_3'),B_45,'#skF_5') = k2_xboole_0(B_45,'#skF_5')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_225,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_28,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_235,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_28])).

tff(c_24,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k4_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_24])).

tff(c_243,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_239])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v3_setfam_1(B_2,A_1)
      | r2_hidden(A_1,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_265,plain,(
    r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_258])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_268,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_265,c_6])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_73,c_268])).

%------------------------------------------------------------------------------
