%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0418+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   44 (  96 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 207 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
            <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_46,axiom,(
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

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_setfam_1(A_12,B_13),k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_30])).

tff(c_33,plain,(
    ! [A_17,B_18] :
      ( k7_setfam_1(A_17,k7_setfam_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_137,plain,(
    ! [A_33,D_34,B_35] :
      ( r2_hidden(k3_subset_1(A_33,D_34),B_35)
      | ~ r2_hidden(D_34,k7_setfam_1(A_33,B_35))
      | ~ m1_subset_1(D_34,k1_zfmisc_1(A_33))
      | ~ m1_subset_1(k7_setfam_1(A_33,B_35),k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [D_34] :
      ( r2_hidden(k3_subset_1('#skF_2',D_34),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(D_34,k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_34,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_137])).

tff(c_146,plain,(
    ! [D_34] :
      ( r2_hidden(k3_subset_1('#skF_2',D_34),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ m1_subset_1(D_34,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36,c_143])).

tff(c_171,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_174,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_194,plain,(
    ! [D_44] :
      ( r2_hidden(k3_subset_1('#skF_2',D_44),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(D_44,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_31])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32,c_202])).

tff(c_213,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_217,plain,(
    ! [A_45,B_46] :
      ( k7_setfam_1(A_45,k7_setfam_1(A_45,B_46)) = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_220,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_214,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_320,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,k7_setfam_1(A_59,B_60))
      | ~ r2_hidden(k3_subset_1(A_59,D_58),B_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(k7_setfam_1(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_322,plain,
    ( r2_hidden('#skF_4',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_214,c_320])).

tff(c_325,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_220,c_20,c_220,c_322])).

tff(c_326,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_325])).

tff(c_329,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_326])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_329])).

%------------------------------------------------------------------------------
