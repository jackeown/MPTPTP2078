%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 557 expanded)
%              Number of leaves         :   35 ( 219 expanded)
%              Depth                    :   19
%              Number of atoms          :  253 (3464 expanded)
%              Number of equality atoms :   90 (1350 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_81,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_81])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_146,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_146])).

tff(c_155,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_152])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_320,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_funct_1(k2_funct_1(C_78))
      | k2_relset_1(A_79,B_80,C_78) != B_80
      | ~ v2_funct_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_78,A_79,B_80)
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_326,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_320])).

tff(c_332,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_52,c_326])).

tff(c_68,plain,(
    ! [E_35] :
      ( r2_hidden(k1_funct_1('#skF_5',E_35),'#skF_2')
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_156,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_164,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_156])).

tff(c_193,plain,(
    ! [B_64,A_65,C_66] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_193])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_164,c_199])).

tff(c_207,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_206])).

tff(c_66,plain,(
    ! [E_35] :
      ( k1_funct_1('#skF_4',k1_funct_1('#skF_5',E_35)) = E_35
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_208,plain,(
    ! [B_67,A_68] :
      ( k1_funct_1(k2_funct_1(B_67),k1_funct_1(B_67,A_68)) = A_68
      | ~ r2_hidden(A_68,k1_relat_1(B_67))
      | ~ v2_funct_1(B_67)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    ! [E_35] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_35) = k1_funct_1('#skF_5',E_35)
      | ~ r2_hidden(k1_funct_1('#skF_5',E_35),k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_208])).

tff(c_235,plain,(
    ! [E_35] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_35) = k1_funct_1('#skF_5',E_35)
      | ~ r2_hidden(k1_funct_1('#skF_5',E_35),k1_relat_1('#skF_4'))
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_50,c_229])).

tff(c_255,plain,(
    ! [E_69] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_69) = k1_funct_1('#skF_5',E_69)
      | ~ r2_hidden(k1_funct_1('#skF_5',E_69),'#skF_2')
      | ~ r2_hidden(E_69,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_235])).

tff(c_263,plain,(
    ! [E_70] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_70) = k1_funct_1('#skF_5',E_70)
      | ~ r2_hidden(E_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_255])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_funct_1(k2_funct_1(B_9),k1_funct_1(B_9,A_8)) = A_8
      | ~ r2_hidden(A_8,k1_relat_1(B_9))
      | ~ v2_funct_1(B_9)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_269,plain,(
    ! [E_70] :
      ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_4')),k1_funct_1('#skF_5',E_70)) = E_70
      | ~ r2_hidden(E_70,k1_relat_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ r2_hidden(E_70,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_16])).

tff(c_373,plain,(
    ! [E_70] :
      ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_4')),k1_funct_1('#skF_5',E_70)) = E_70
      | ~ r2_hidden(E_70,k1_relat_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ r2_hidden(E_70,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_269])).

tff(c_374,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_423,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_374])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_423])).

tff(c_429,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_84,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_81])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_84])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_163,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_156])).

tff(c_196,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_193])).

tff(c_202,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_163,c_196])).

tff(c_203,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_202])).

tff(c_304,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),k1_relat_1(A_74))
      | B_75 = A_74
      | k1_relat_1(B_75) != k1_relat_1(A_74)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_310,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_1'('#skF_5',B_75),'#skF_3')
      | B_75 = '#skF_5'
      | k1_relat_1(B_75) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_304])).

tff(c_317,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_1'('#skF_5',B_75),'#skF_3')
      | B_75 = '#skF_5'
      | k1_relat_1(B_75) != '#skF_3'
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_58,c_203,c_310])).

tff(c_262,plain,(
    ! [E_35] :
      ( k1_funct_1(k2_funct_1('#skF_4'),E_35) = k1_funct_1('#skF_5',E_35)
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_255])).

tff(c_351,plain,(
    ! [B_84,A_85] :
      ( k1_funct_1(B_84,'#skF_1'(A_85,B_84)) != k1_funct_1(A_85,'#skF_1'(A_85,B_84))
      | B_84 = A_85
      | k1_relat_1(B_84) != k1_relat_1(A_85)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_355,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_1'(A_85,k2_funct_1('#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(A_85,k2_funct_1('#skF_4')))
      | k2_funct_1('#skF_4') = A_85
      | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(A_85)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85)
      | ~ r2_hidden('#skF_1'(A_85,k2_funct_1('#skF_4')),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_351])).

tff(c_369,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_1'(A_85,k2_funct_1('#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(A_85,k2_funct_1('#skF_4')))
      | k2_funct_1('#skF_4') = A_85
      | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(A_85)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85)
      | ~ r2_hidden('#skF_1'(A_85,k2_funct_1('#skF_4')),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_355])).

tff(c_557,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_1'(A_85,k2_funct_1('#skF_4'))) != k1_funct_1('#skF_5','#skF_1'(A_85,k2_funct_1('#skF_4')))
      | k2_funct_1('#skF_4') = A_85
      | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85)
      | ~ r2_hidden('#skF_1'(A_85,k2_funct_1('#skF_4')),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_369])).

tff(c_560,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_557])).

tff(c_562,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_58,c_203,c_560])).

tff(c_563,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_562])).

tff(c_575,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k2_funct_1('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_578,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3'
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_317,c_575])).

tff(c_581,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_332,c_578])).

tff(c_582,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_581])).

tff(c_585,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_582])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_50,c_155,c_585])).

tff(c_589,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_593,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_589])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_50,c_155,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.53  
% 3.13/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.53  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.13/1.53  
% 3.13/1.53  %Foreground sorts:
% 3.13/1.53  
% 3.13/1.53  
% 3.13/1.53  %Background operators:
% 3.13/1.53  
% 3.13/1.53  
% 3.13/1.53  %Foreground operators:
% 3.13/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.13/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.13/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.13/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.13/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.13/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.13/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.53  
% 3.13/1.55  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.13/1.55  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_2)).
% 3.13/1.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.13/1.55  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.55  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.13/1.55  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.13/1.55  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.13/1.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.55  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.13/1.55  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 3.13/1.55  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.13/1.55  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.13/1.55  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_81, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.55  tff(c_87, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_81])).
% 3.13/1.55  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87])).
% 3.13/1.55  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_50, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_52, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_146, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.13/1.55  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_146])).
% 3.13/1.55  tff(c_155, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_152])).
% 3.13/1.55  tff(c_12, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.55  tff(c_44, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.13/1.55  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_320, plain, (![C_78, A_79, B_80]: (v1_funct_1(k2_funct_1(C_78)) | k2_relset_1(A_79, B_80, C_78)!=B_80 | ~v2_funct_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_78, A_79, B_80) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.13/1.55  tff(c_326, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_320])).
% 3.13/1.55  tff(c_332, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_52, c_326])).
% 3.13/1.55  tff(c_68, plain, (![E_35]: (r2_hidden(k1_funct_1('#skF_5', E_35), '#skF_2') | ~r2_hidden(E_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_156, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.13/1.55  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_156])).
% 3.13/1.55  tff(c_193, plain, (![B_64, A_65, C_66]: (k1_xboole_0=B_64 | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.13/1.55  tff(c_199, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_193])).
% 3.13/1.55  tff(c_206, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_164, c_199])).
% 3.13/1.55  tff(c_207, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_206])).
% 3.13/1.55  tff(c_66, plain, (![E_35]: (k1_funct_1('#skF_4', k1_funct_1('#skF_5', E_35))=E_35 | ~r2_hidden(E_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_208, plain, (![B_67, A_68]: (k1_funct_1(k2_funct_1(B_67), k1_funct_1(B_67, A_68))=A_68 | ~r2_hidden(A_68, k1_relat_1(B_67)) | ~v2_funct_1(B_67) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.55  tff(c_229, plain, (![E_35]: (k1_funct_1(k2_funct_1('#skF_4'), E_35)=k1_funct_1('#skF_5', E_35) | ~r2_hidden(k1_funct_1('#skF_5', E_35), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(E_35, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_208])).
% 3.13/1.55  tff(c_235, plain, (![E_35]: (k1_funct_1(k2_funct_1('#skF_4'), E_35)=k1_funct_1('#skF_5', E_35) | ~r2_hidden(k1_funct_1('#skF_5', E_35), k1_relat_1('#skF_4')) | ~r2_hidden(E_35, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_50, c_229])).
% 3.13/1.55  tff(c_255, plain, (![E_69]: (k1_funct_1(k2_funct_1('#skF_4'), E_69)=k1_funct_1('#skF_5', E_69) | ~r2_hidden(k1_funct_1('#skF_5', E_69), '#skF_2') | ~r2_hidden(E_69, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_235])).
% 3.13/1.55  tff(c_263, plain, (![E_70]: (k1_funct_1(k2_funct_1('#skF_4'), E_70)=k1_funct_1('#skF_5', E_70) | ~r2_hidden(E_70, '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_255])).
% 3.13/1.55  tff(c_16, plain, (![B_9, A_8]: (k1_funct_1(k2_funct_1(B_9), k1_funct_1(B_9, A_8))=A_8 | ~r2_hidden(A_8, k1_relat_1(B_9)) | ~v2_funct_1(B_9) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.55  tff(c_269, plain, (![E_70]: (k1_funct_1(k2_funct_1(k2_funct_1('#skF_4')), k1_funct_1('#skF_5', E_70))=E_70 | ~r2_hidden(E_70, k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~r2_hidden(E_70, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_16])).
% 3.13/1.55  tff(c_373, plain, (![E_70]: (k1_funct_1(k2_funct_1(k2_funct_1('#skF_4')), k1_funct_1('#skF_5', E_70))=E_70 | ~r2_hidden(E_70, k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~r2_hidden(E_70, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_269])).
% 3.13/1.55  tff(c_374, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_373])).
% 3.13/1.55  tff(c_423, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_374])).
% 3.13/1.55  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_423])).
% 3.13/1.55  tff(c_429, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_373])).
% 3.13/1.55  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_84, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_81])).
% 3.13/1.55  tff(c_90, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_84])).
% 3.13/1.55  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.13/1.55  tff(c_163, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_156])).
% 3.13/1.55  tff(c_196, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_193])).
% 3.13/1.55  tff(c_202, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_163, c_196])).
% 3.13/1.55  tff(c_203, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_202])).
% 3.13/1.55  tff(c_304, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), k1_relat_1(A_74)) | B_75=A_74 | k1_relat_1(B_75)!=k1_relat_1(A_74) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.55  tff(c_310, plain, (![B_75]: (r2_hidden('#skF_1'('#skF_5', B_75), '#skF_3') | B_75='#skF_5' | k1_relat_1(B_75)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_75) | ~v1_relat_1(B_75) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_304])).
% 3.13/1.55  tff(c_317, plain, (![B_75]: (r2_hidden('#skF_1'('#skF_5', B_75), '#skF_3') | B_75='#skF_5' | k1_relat_1(B_75)!='#skF_3' | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_58, c_203, c_310])).
% 3.13/1.55  tff(c_262, plain, (![E_35]: (k1_funct_1(k2_funct_1('#skF_4'), E_35)=k1_funct_1('#skF_5', E_35) | ~r2_hidden(E_35, '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_255])).
% 3.13/1.55  tff(c_351, plain, (![B_84, A_85]: (k1_funct_1(B_84, '#skF_1'(A_85, B_84))!=k1_funct_1(A_85, '#skF_1'(A_85, B_84)) | B_84=A_85 | k1_relat_1(B_84)!=k1_relat_1(A_85) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.55  tff(c_355, plain, (![A_85]: (k1_funct_1(A_85, '#skF_1'(A_85, k2_funct_1('#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(A_85, k2_funct_1('#skF_4'))) | k2_funct_1('#skF_4')=A_85 | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(A_85) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85) | ~r2_hidden('#skF_1'(A_85, k2_funct_1('#skF_4')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_262, c_351])).
% 3.13/1.55  tff(c_369, plain, (![A_85]: (k1_funct_1(A_85, '#skF_1'(A_85, k2_funct_1('#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(A_85, k2_funct_1('#skF_4'))) | k2_funct_1('#skF_4')=A_85 | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(A_85) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85) | ~r2_hidden('#skF_1'(A_85, k2_funct_1('#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_355])).
% 3.13/1.55  tff(c_557, plain, (![A_85]: (k1_funct_1(A_85, '#skF_1'(A_85, k2_funct_1('#skF_4')))!=k1_funct_1('#skF_5', '#skF_1'(A_85, k2_funct_1('#skF_4'))) | k2_funct_1('#skF_4')=A_85 | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85) | ~r2_hidden('#skF_1'(A_85, k2_funct_1('#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_369])).
% 3.13/1.55  tff(c_560, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_557])).
% 3.13/1.55  tff(c_562, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_58, c_203, c_560])).
% 3.13/1.55  tff(c_563, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_562])).
% 3.13/1.55  tff(c_575, plain, (~r2_hidden('#skF_1'('#skF_5', k2_funct_1('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_563])).
% 3.13/1.55  tff(c_578, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3' | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_317, c_575])).
% 3.13/1.55  tff(c_581, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_332, c_578])).
% 3.13/1.55  tff(c_582, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_581])).
% 3.13/1.55  tff(c_585, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_582])).
% 3.13/1.55  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_50, c_155, c_585])).
% 3.13/1.55  tff(c_589, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitRight, [status(thm)], [c_563])).
% 3.13/1.55  tff(c_593, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_589])).
% 3.13/1.55  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_50, c_155, c_593])).
% 3.13/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.55  
% 3.13/1.55  Inference rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Ref     : 3
% 3.13/1.55  #Sup     : 108
% 3.13/1.55  #Fact    : 0
% 3.13/1.55  #Define  : 0
% 3.13/1.55  #Split   : 5
% 3.13/1.55  #Chain   : 0
% 3.13/1.55  #Close   : 0
% 3.13/1.55  
% 3.13/1.55  Ordering : KBO
% 3.13/1.55  
% 3.13/1.55  Simplification rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Subsume      : 13
% 3.13/1.55  #Demod        : 99
% 3.13/1.55  #Tautology    : 46
% 3.13/1.55  #SimpNegUnit  : 7
% 3.13/1.55  #BackRed      : 2
% 3.13/1.55  
% 3.13/1.55  #Partial instantiations: 0
% 3.13/1.55  #Strategies tried      : 1
% 3.13/1.55  
% 3.13/1.55  Timing (in seconds)
% 3.13/1.55  ----------------------
% 3.13/1.56  Preprocessing        : 0.37
% 3.13/1.56  Parsing              : 0.20
% 3.13/1.56  CNF conversion       : 0.02
% 3.13/1.56  Main loop            : 0.33
% 3.13/1.56  Inferencing          : 0.12
% 3.13/1.56  Reduction            : 0.11
% 3.13/1.56  Demodulation         : 0.07
% 3.13/1.56  BG Simplification    : 0.02
% 3.13/1.56  Subsumption          : 0.06
% 3.13/1.56  Abstraction          : 0.02
% 3.13/1.56  MUC search           : 0.00
% 3.13/1.56  Cooper               : 0.00
% 3.13/1.56  Total                : 0.74
% 3.13/1.56  Index Insertion      : 0.00
% 3.13/1.56  Index Deletion       : 0.00
% 3.13/1.56  Index Matching       : 0.00
% 3.13/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
