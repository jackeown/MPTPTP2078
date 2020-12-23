%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1108+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:25 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 287 expanded)
%              Number of leaves         :   33 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 (1013 expanded)
%              Number of equality atoms :   31 ( 103 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k5_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v1_funct_1(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))
                      & v1_funct_2(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),u1_struct_0(k1_pre_topc(A,D)),u1_struct_0(B))
                      & m1_subset_1(k5_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(A,D)),u1_struct_0(B)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_51,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_721,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_partfun1(A_182,B_183,C_184,D_185) = k7_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_725,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_185) = k7_relat_1('#skF_3',D_185)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_721])).

tff(c_734,plain,(
    ! [D_185] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_185) = k7_relat_1('#skF_3',D_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_725])).

tff(c_1006,plain,(
    ! [B_235,A_236,D_237,C_238] :
      ( k1_xboole_0 = B_235
      | v1_funct_2(k2_partfun1(A_236,B_235,D_237,C_238),C_238,B_235)
      | ~ r1_tarski(C_238,A_236)
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235)))
      | ~ v1_funct_2(D_237,A_236,B_235)
      | ~ v1_funct_1(D_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1020,plain,(
    ! [C_238] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',C_238),C_238,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_238,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_1006])).

tff(c_1040,plain,(
    ! [C_238] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k7_relat_1('#skF_3',C_238),C_238,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_238,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_734,c_1020])).

tff(c_1081,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1040])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1115,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_10])).

tff(c_1123,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1115])).

tff(c_1124,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1123])).

tff(c_1128,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1124])).

tff(c_1132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1128])).

tff(c_1135,plain,(
    ! [C_246] :
      ( v1_funct_2(k7_relat_1('#skF_3',C_246),C_246,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_246,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_1040])).

tff(c_209,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k2_partfun1(A_83,B_84,C_85,D_86) = k7_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_211,plain,(
    ! [D_86] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_86) = k7_relat_1('#skF_3',D_86)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_209])).

tff(c_217,plain,(
    ! [D_86] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_86) = k7_relat_1('#skF_3',D_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_211])).

tff(c_400,plain,(
    ! [B_127,A_128,D_129,C_130] :
      ( k1_xboole_0 = B_127
      | v1_funct_2(k2_partfun1(A_128,B_127,D_129,C_130),C_130,B_127)
      | ~ r1_tarski(C_130,A_128)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_2(D_129,A_128,B_127)
      | ~ v1_funct_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_408,plain,(
    ! [C_130] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',C_130),C_130,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_130,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_400])).

tff(c_421,plain,(
    ! [C_130] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k7_relat_1('#skF_3',C_130),C_130,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_130,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_217,c_408])).

tff(c_437,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_462,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_10])).

tff(c_470,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_462])).

tff(c_471,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_470])).

tff(c_475,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_471])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_475])).

tff(c_481,plain,(
    u1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_605,plain,(
    ! [B_171,A_172,D_173,C_174] :
      ( k1_xboole_0 = B_171
      | m1_subset_1(k2_partfun1(A_172,B_171,D_173,C_174),k1_zfmisc_1(k2_zfmisc_1(C_174,B_171)))
      | ~ r1_tarski(C_174,A_172)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2(D_173,A_172,B_171)
      | ~ v1_funct_1(D_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_631,plain,(
    ! [D_86] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1(k7_relat_1('#skF_3',D_86),k1_zfmisc_1(k2_zfmisc_1(D_86,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(D_86,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_605])).

tff(c_648,plain,(
    ! [D_86] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1(k7_relat_1('#skF_3',D_86),k1_zfmisc_1(k2_zfmisc_1(D_86,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(D_86,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_631])).

tff(c_650,plain,(
    ! [D_175] :
      ( m1_subset_1(k7_relat_1('#skF_3',D_175),k1_zfmisc_1(k2_zfmisc_1(D_175,u1_struct_0('#skF_2'))))
      | ~ r1_tarski(D_175,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_648])).

tff(c_143,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k2_partfun1(A_63,B_64,C_65,D_66) = k7_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [D_66] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_66) = k7_relat_1('#skF_3',D_66)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_151,plain,(
    ! [D_66] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_66) = k7_relat_1('#skF_3',D_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_145])).

tff(c_126,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( v1_funct_1(k2_partfun1(A_54,B_55,C_56,D_57))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [D_57] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_57))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_126])).

tff(c_134,plain,(
    ! [D_57] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128])).

tff(c_153,plain,(
    ! [D_57] : v1_funct_1(k7_relat_1('#skF_3',D_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_134])).

tff(c_77,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k5_relset_1(A_43,B_44,C_45,D_46) = k7_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [D_46] : k5_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_46) = k7_relat_1('#skF_3',D_46) ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_65,plain,(
    ! [A_41,B_42] :
      ( u1_struct_0(k1_pre_topc(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_4')) = '#skF_4'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_76,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72])).

tff(c_34,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k1_pre_topc('#skF_1','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_105,plain,
    ( ~ m1_subset_1(k7_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_relat_1('#skF_3','#skF_4'),'#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_76,c_83,c_76,c_34])).

tff(c_106,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_106])).

tff(c_166,plain,
    ( ~ v1_funct_2(k7_relat_1('#skF_3','#skF_4'),'#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k7_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_198,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_660,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_650,c_198])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_660])).

tff(c_682,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_3','#skF_4'),'#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_1138,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1135,c_682])).

tff(c_1142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1138])).

%------------------------------------------------------------------------------
